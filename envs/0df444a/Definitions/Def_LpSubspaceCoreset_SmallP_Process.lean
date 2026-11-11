-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Process
-- name    : LpSubspaceCoreset_SmallP_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:31.186795+00:00
-- url     : https://prove2.me/theorems/7e89ccf9-c01f-46a5-9fec-521d53ba9a4a
-- title:
--   The duality map J_p, L2(ν) covers and the absolute Rademacher complexity
-- statement:
--   For $x$ in a real inner-product space, the **duality map** is $J_p(x)=\|x\|^{p-2}x$ for $x\neq0$ and $J_p(0)=0$ (§2.6); at $p=1$, $J_1(x)=x/\|x\|$.
--
--   For a law $\nu$ on a finite index set and real functions $f,g$ on it, $\|f-g\|_{L_2(\nu)}=\big(\sum_i\nu_i|f(i)-g(i)|^2\big)^{1/2}$. A **$\delta$-cover** of a class $G$ is a set $\mathcal N\subseteq G$ such that every $g\in G$ is within $L_2(\nu)$-distance $\delta$ of some element of $\mathcal N$; the covering number $N(\delta,G,L_2(\nu))$ is the least cardinality of a $\delta$-cover. The **empirical law** of a sample $I_1,\dots,I_m$ gives index $i$ the weight $\#\{s:I_s=i\}/m$.
--
--   The **absolute Rademacher complexity** of $G$ is
--   $$R^{\mathrm{abs}}_m(G)=\mathbb E_{I,\varepsilon}\sup_{g\in G}\Big|\frac1m\sum_{s=1}^m\varepsilon_s\,g(I_s)\Big|,$$
--   with $I_1,\dots,I_m$ independent draws from $q$ and independent uniform signs $\varepsilon_s$; $R^{\mathrm{abs}}_m(G\mid I_1,\dots,I_m)$ is the same quantity with the expectation over the signs only (§2.5).
--
--   **Formalization Note** Both expectations are finite sums (over $2^m$ sign vectors and over $[n]^m$ weighted by $\prod_s q_{I_s}$) and the supremum is taken in $[0,\infty]$, so an unbounded class has complexity $\infty$, never a junk $0$. A bound $\log N(\delta,G,L_2(\nu))\le X$ is stated as "some finite $\delta$-cover $\mathcal N\subseteq G$ has $\log|\mathcal N|\le X$", which never turns an infinite covering number into $0$.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 13–14, §2.5 and §2.6

import Mathlib

namespace LpSubspaceCoreset.SmallP

open scoped ENNReal

/-!
# The duality map, `L2(ν)` covers and the absolute Rademacher complexity

Lin, Mirrokni, Woodruff, arXiv:2608.26047, §2.5 (pp. 13–14) and §2.6 (p. 14).

* `J_p(x) = ‖x‖^{p−2} x` for `x ≠ 0` and `J_p(0) = 0`, in a real inner-product space
  (at `p = 1`, `J_1(x) = x/‖x‖`).
* Functions on a finite index set `ι` (the row indices); `ν` is a law on `ι` given by its
  weights. `‖f − g‖_{L2(ν)} = (Σ_i ν_i |f(i) − g(i)|²)^{1/2}`.
* `IsCover ν δ G N`: `N` is a finite subset of `G` and every `g ∈ G` is within `L2(ν)`-distance
  `δ` of some element of `N`. The covering number `N(δ, G, L2(ν))` is the least cardinality of
  such an `N`, so "`log N(δ, G, L2(ν)) ≤ X`" is stated as "some cover `N` has `log |N| ≤ X`",
  which never turns an infinite covering number into `0`.
* The empirical law of a sample `I : Fin m → ι` gives `i` the weight `#{s : I_s = i}/m`.
* `R^abs_m(G | I_1, …, I_m) = E_ε sup_{g∈G} |m⁻¹ Σ_s ε_s g(I_s)|` over independent uniform signs:
  the finite average over the `2^m` sign vectors, with the supremum taken in `ℝ≥0∞` (so an
  unbounded class has complexity `∞`, never a junk `0`). `R^abs_m(G)` additionally averages over
  `I_1, …, I_m` drawn independently from `q`: a finite sum weighted by `Π_s q_{I_s}`.
-/

/-- The duality map `J_p(x) = ‖x‖^{p−2} x` (`x ≠ 0`), `J_p(0) = 0`. -/
noncomputable def dualityMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ℝ) (x : H) : H :=
  by classical exact if x = 0 then 0 else ‖x‖ ^ (p - 2) • x

/-- `‖f − g‖_{L2(ν)} = (Σ_i ν_i |f(i) − g(i)|²)^{1/2}`. -/
noncomputable def l2Dist {ι : Type*} [Fintype ι] (ν : ι → ℝ) (f g : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, ν i * (f i - g i) ^ 2)

/-- `ν` is a probability law on `ι`. -/
def IsProbLaw {ι : Type*} [Fintype ι] (ν : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ ν i) ∧ ∑ i, ν i = 1

/-- `N` is an internal `δ`-cover of the class `G` in `L2(ν)`. -/
def IsCover {ι : Type*} [Fintype ι] (ν : ι → ℝ) (δ : ℝ) (G : Set (ι → ℝ))
    (N : Finset (ι → ℝ)) : Prop :=
  (↑N ⊆ G) ∧ ∀ g ∈ G, ∃ g' ∈ N, l2Dist ν g g' ≤ δ

/-- The empirical law `m⁻¹ Σ_s δ_{I_s}` of the sample `I`. -/
noncomputable def empiricalLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (I : Fin m → ι) : ι → ℝ :=
  fun i => ((Finset.univ.filter fun s => I s = i).card : ℝ) / m

/-- The sign `±1` encoded by a boolean. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- The conditional absolute Rademacher complexity
`R^abs_m(G | I_1, …, I_m) = E_ε sup_{g ∈ G} |m⁻¹ Σ_s ε_s g(I_s)|`. -/
noncomputable def radAbsCond {ι : Type*} {m : ℕ} (G : Set (ι → ℝ)) (I : Fin m → ι) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ m)⁻¹ * ∑ σ : Fin m → Bool,
    ⨆ g ∈ G, ENNReal.ofReal |(1 / (m : ℝ)) * ∑ s, signOf (σ s) * g (I s)|

/-- The absolute Rademacher complexity `R^abs_m(G) = E_{I,ε} sup_{g ∈ G} |m⁻¹ Σ_s ε_s g(I_s)|`
with `I_1, …, I_m` independent draws from `q`. -/
noncomputable def radAbs {ι : Type*} [Fintype ι] (q : ι → ℝ) (G : Set (ι → ℝ)) (m : ℕ) :
    ℝ≥0∞ :=
  ∑ I : Fin m → ι, ENNReal.ofReal (∏ s, q (I s)) * radAbsCond G I

end LpSubspaceCoreset.SmallP


