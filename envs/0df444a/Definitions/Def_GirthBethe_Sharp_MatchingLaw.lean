-- Prove2me | Definitions.Def_GirthBethe_Sharp_MatchingLaw
-- name    : GirthBethe_Sharp_MatchingLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:17.21196+00:00
-- url     : https://prove2.me/theorems/936bf839-94c4-4f71-98ef-460ac10a385d
-- title:
--   (3.1)–(3.5), Definition 4.1 — random perfect matchings, $\Phi_G$, $\Phi_0$, $\mathrm{gap}(u)$ and $J^\pm$
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite bipartite graph and $\mu$ a probability law on its perfect matchings $M$ (arbitrary; not necessarily a Gibbs law). Fix an integer $g$.
--
--   1. (3.2) Edge marginals $p_e=P_{M\sim\mu}(e\in M)$; $X_u\in R$ is the partner of $u\in L$, $(X^{-1})_w\in L$ the partner of $w\in R$; $E_e=\mathbf 1_{\{e\in M\}}$; $Z_v$ is the matched neighbour of $v\in V$, identified with the edge of $M$ at $v$, so $\mathcal L(Z_v)=p_v$.
--   2. (3.3) Conditional marginals $p^{X_u=w}_e=P(e\in M\mid X_u=w)$ (the unconditional marginal when $P(X_u=w)=0$).
--   3. (3.1) $\Phi_G(p)=H_B(p)+\frac2g\sum_{v\in V}F(p_v)$.
--   4. (3.5) $\Phi_0(p)=\frac1g\sum_{v\in V}H_c(p_v)+\frac{g-2}{2g}\sum_{v\in V}S(p_v)$.
--   5. (3.4) $\mathrm{gap}(u)=\Phi(p)-\mathbb E_{X_u}\Phi(p^{X_u})-H(X_u)$, where $\mathbb E_{X_u}\Phi(p^{X_u})=\sum_w P(X_u=w)\,\Phi(p^{X_u=w})$; $u$ is good if $\mathrm{gap}(u)\ge0$.
--   6. (Definition 4.1) For a fixed $\star\in L$ and every edge $e$,
--   $$J^+_e=p_e\,\mathrm{KL}\big(\mathcal L(X_\star\mid E_e=1)\,\|\,\mathcal L(X_\star)\big),\qquad J^-_e=(1-p_e)\,\mathrm{KL}\big(\mathcal L(X_\star\mid E_e=0)\,\|\,\mathcal L(X_\star)\big),$$
--   with $J^+_e=0$ when $p_e=0$ and $J^-_e=0$ when $p_e=1$; and $J^\pm_v=\sum_{e\ni v}J^\pm_e$.
--
--   These quantities carry the paper's induction (good vertex) and its girth argument.
--
--   **Formalization Note** Divergences are finite here (a posterior given a positive-probability event is absolutely continuous with respect to the prior), so $J^\pm_e$ is real and uses the real value of the extended-real KL.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 9, equations (3.1)–(3.5) (pp. 9–10), Definition 3.2 (p. 10), Definition 4.1 (p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_LocalFunctionals
import Definitions.Def_GirthBethe_Sharp_FiniteInfo
import Definitions.Def_GirthBethe_Sharp_BipartiteGraph

open Finset

namespace GirthBethe.Sharp

/-! Random perfect matchings and the quantities of §§3–4 of Jain–Dong, STOC 2027 submission #705:
edge marginals (3.2), the matched-partner variables `X_u`, `(X⁻¹)_w`, `Z_v`, conditional
marginals (3.3), the potentials `Φ_G` (3.1) and `Φ₀` (3.5), `gap(u)` (3.4), and the edge weights
`J_e^±`, `J_v^±` of Definition 4.1. A law `μ` on perfect matchings is a vector in
`stdSimplex ℝ (PerfMatching E)`, arbitrary (not necessarily a Gibbs law, zeros allowed). -/

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  {E : Finset (L × R)}

/-- The matched partner `X_u ∈ R` of `u ∈ L`. -/
def matchX (u : L) : PerfMatching E → R := fun σ => σ.1 u

/-- The matched partner `(X⁻¹)_w ∈ L` of `w ∈ R`. -/
def matchXinv (w : R) : PerfMatching E → L := fun σ => σ.1.symm w

/-- The indicator `E_e = 1_{e ∈ M}` (`true` iff `e ∈ M`). -/
def edgeInd (e : Edge E) : PerfMatching E → Bool := fun σ => decide (σ.1 e.1.1 = e.1.2)

/-- The matched neighbour `Z_v` of a vertex `v`, identified with the edge of `M` at `v`
(`Z_v = X_v` for `v ∈ L`, `Z_v = (X⁻¹)_v` for `v ∈ R`). -/
def matchZ : (v : L ⊕ R) → PerfMatching E → IncEdge E v
  | Sum.inl u, σ => ⟨⟨(u, σ.1 u), σ.2 u⟩, rfl⟩
  | Sum.inr w, σ => ⟨⟨(σ.1.symm w, w), by simpa using σ.2 (σ.1.symm w)⟩, rfl⟩

/-- Edge marginals `p_e = P_{M∼μ}(e ∈ M)` (3.2). -/
noncomputable def edgeMarg (μ : PerfMatching E → ℝ) : Edge E → ℝ :=
  fun e => law μ (edgeInd e) true

/-- Conditional edge marginals `p_e^{X_u = w} = P(e ∈ M | X_u = w)` (3.3); for
`P(X_u = w) = 0` the unconditional marginal is used (weight zero everywhere below). -/
noncomputable def condMarg (μ : PerfMatching E → ℝ) (u : L) (w : R) : Edge E → ℝ :=
  fun e => condLaw μ (edgeInd e) (matchX u) w true

/-- The potential `Φ_G(p) = H_B(p) + (2/g) ∑_v F(p_v)` (3.1). -/
noncomputable def phi (g : ℕ) (E : Finset (L × R)) (p : Edge E → ℝ) : ℝ :=
  betheEntropy E p + (2 / (g : ℝ)) * ∑ v : L ⊕ R, anariRezaei (localVec p v)

/-- The potential `Φ₀(p) = (1/g) ∑_v Hc(p_v) + ((g-2)/(2g)) ∑_v S(p_v)` (3.5). -/
noncomputable def phi0 (g : ℕ) (E : Finset (L × R)) (p : Edge E → ℝ) : ℝ :=
  (1 / (g : ℝ)) * ∑ v : L ⊕ R, compEntropy (localVec p v) +
    (((g : ℝ) - 2) / (2 * (g : ℝ))) * ∑ v : L ⊕ R, localBethe (localVec p v)

/-- `gap(u) = Φ(p) - E_{X_u} Φ(p^{X_u}) - H(X_u)` (3.4). -/
noncomputable def gap (g : ℕ) (μ : PerfMatching E → ℝ) (u : L) : ℝ :=
  phi g E (edgeMarg μ) - ∑ w, law μ (matchX u) w * phi g E (condMarg μ u w) -
    shannon (law μ (matchX u))

/-- `J_e^+ = p_e KL(L(X_⋆ | E_e = 1) ‖ L(X_⋆))`, set to `0` when `p_e = 0` (Definition 4.1).
The divergence is finite here (a positive-probability posterior is absolutely continuous with
respect to the prior), so its real value is taken. -/
noncomputable def jPlus (μ : PerfMatching E → ℝ) (star : L) (e : Edge E) : ℝ :=
  if edgeMarg μ e = 0 then 0
  else edgeMarg μ e *
    (klDiv (condLaw μ (matchX star) (edgeInd e) true) (law μ (matchX star))).toReal

/-- `J_e^- = (1 - p_e) KL(L(X_⋆ | E_e = 0) ‖ L(X_⋆))`, set to `0` when `p_e = 1`
(Definition 4.1); finite as for `J_e^+`. -/
noncomputable def jMinus (μ : PerfMatching E → ℝ) (star : L) (e : Edge E) : ℝ :=
  if edgeMarg μ e = 1 then 0
  else (1 - edgeMarg μ e) *
    (klDiv (condLaw μ (matchX star) (edgeInd e) false) (law μ (matchX star))).toReal

/-- `J_v^+ = ∑_{e ∋ v} J_e^+` (Definition 4.1). -/
noncomputable def jPlusV (μ : PerfMatching E → ℝ) (star : L) (v : L ⊕ R) : ℝ :=
  vertexWeight (jPlus μ star) v

/-- `J_v^- = ∑_{e ∋ v} J_e^-` (Definition 4.1). -/
noncomputable def jMinusV (μ : PerfMatching E → ℝ) (star : L) (v : L ⊕ R) : ℝ :=
  vertexWeight (jMinus μ star) v

end GirthBethe.Sharp


