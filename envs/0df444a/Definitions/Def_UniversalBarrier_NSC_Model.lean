-- Prove2me | Definitions.Def_UniversalBarrier_NSC_Model
-- name    : UniversalBarrier_NSC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:08.115034+00:00
-- url     : https://prove2.me/theorems/32a4eec7-8b36-4c13-a3df-b100a7182452
-- title:
--   §2, Definitions 3–5, (10), §4 — proper convex domains, polar sets, the universal barrier, marginal densities, moments, s-concavity, 1/(k−1)-affine densities, Ξ, f₀, g, ℓ
-- statement:
--   This file sets up the objects of Lee and Yue, *Universal Barrier is $n$-Self-Concordant*, on $\mathbb R^n$ with the Euclidean inner product $y^{\mathsf T}z$ and Lebesgue measure $\mathrm{Vol}_n$.
--
--   **Proper convex domains.** A *convex domain* is a convex set $K\subseteq\mathbb R^n$ with non-empty interior. It is *proper* if it contains no line $\{x+tv:t\in\mathbb R\}$ with $v\neq0$. $K$ is not assumed closed or bounded.
--
--   **Polar sets and the universal barrier** (Definition 3). For $x\in\mathbb R^n$ the polar set of $K$ with respect to $x$ is
--   $$K^\circ(x)=\{y\in\mathbb R^n:\ y^{\mathsf T}(z-x)\le1\ \text{ for all } z\in K\},$$
--   and the *universal barrier* of $K$ is $\varphi(x)=\log\mathrm{Vol}_n(K^\circ(x))$ for $x\in\operatorname{int}(K)$.
--
--   **Marginal densities** (Definition 4). For a convex body $L$ (compact convex with non-empty interior) and a direction $h\neq0$, $p(L,h;\cdot)$ is the density of $y^{\mathsf T}h$ when $y$ is uniform on $L$: it is proportional to the $(n-1)$-dimensional volume of the slice $\{y\in L:\ y^{\mathsf T}h=t\}$ and integrates to $1$.
--
--   **Moments** (§2.2). For a density $p$ on $\mathbb R$,
--   $$\mu_1(p)=\int t\,p(t)\,dt,\qquad \mu_2^2(p)=\int (t-\mu_1(p))^2p(t)\,dt,\qquad \mu_3^3(p)=\int (t-\mu_1(p))^3p(t)\,dt,$$
--   and $\mu_2^3(p)=(\mu_2^2(p))^{3/2}$.
--
--   **$s$-concavity** (Definition 5). For an integer $m\ge1$, a density $p$ is $\tfrac1m$-concave if for all $t_1,t_2$ with $p(t_1),p(t_2)>0$ and all $\lambda\in[0,1]$,
--   $$p(\lambda t_1+(1-\lambda)t_2)\ \ge\ \bigl(\lambda\,p(t_1)^{1/m}+(1-\lambda)\,p(t_2)^{1/m}\bigr)^{m};$$
--   for $m=0$ ($s=+\infty$) the right-hand side is $\max\{p(t_1),p(t_2)\}$.
--
--   **The $\tfrac1{k-1}$-affine family $\mathcal Q$** ((10), p. 7): densities
--   $$q(t)=\frac{(\alpha t+\beta)^{k-1}\,\mathbb 1_{[a,b]}(t)}{\int_a^b(\alpha u+\beta)^{k-1}\,du}$$
--   with $a<b$, $\alpha t+\beta\ge0$ on $[a,b]$ and a positive denominator. For such densities $\Xi(p)=\bigl|\mu_3^3(p)/\mu_2^3(p)\bigr|$ (p. 13).
--
--   **Auxiliary functions.** For an integer $k$ and real $\gamma$:
--   $$f_0(\gamma)=k(\gamma^k-1)\bigl[k(k+1)(\gamma^{k+2}-1)-2k(k+2)(\gamma^{k+1}-1)+(k+1)(k+2)(\gamma^k-1)\bigr]-(k+1)\bigl[k(\gamma^{k+1}-1)-(k+1)(\gamma^k-1)\bigr]^2$$
--   (§4.1.7, p. 12), and $g(\gamma,k)$ is the polynomial of (35), p. 17:
--   $$g(\gamma,k)=4(k-1)^2\bigl((k+1)^2(\gamma^k-1)(\gamma^{k+2}-1)-k(k+2)(\gamma^{k+1}-1)^2\bigr)^3-\bigl(2k^2(k+2)(k+3)(\gamma^{k+1}-1)^3+(k+2)(k+1)^3(\gamma^k-1)^2(\gamma^{k+3}-1)-3k(k+3)(k+1)^2(\gamma^k-1)(\gamma^{k+1}-1)(\gamma^{k+2}-1)\bigr)^2.$$
--   Finally $c_n=(n-1)/(2\sqrt n)$ and $\ell(t)=(2t^3+6t+4c_n)/(1+t^2)^{3/2}$ (p. 5).
--
--   These are the objects of Theorem 2 and of the proof of Proposition 1.
--
--   **Formalization Note.** The space is `EuclideanSpace ℝ (Fin n)`. The universal barrier is a total function whose values off $\operatorname{int}(K)$ are junk (an infinite volume becomes $0$ and $\log 0=0$); every statement uses it only on $\operatorname{int}(K)$ or in limits within $\operatorname{int}(K)$. Three corrections to the page, each necessary: (1) Definition 5 read literally (for all $t_1,t_2\in\mathbb R$) is satisfied by no probability density, so $t_1,t_2$ range over the support points $\{p>0\}$, which is the paper's own usage ("on its support", Theorem 1; $t_1,t_2\in S$, p. 6); (2) the marginal of Definition 4 is normalized by its own integral, because $\mathrm{Vol}_{n-1}(\text{slice})/\mathrm{Vol}_n(L)$ integrates to $1/\|h\|$ and because the published section measure is Mathlib's unnormalized Hausdorff measure; (3) the family (10) is taken with $a<b$ (the paper's $a=b$ makes the denominator $0$; it treats that Dirac case separately). The moments are Bochner integrals.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, pp. 2–5, 7, 12, 13, 17, §2.1–§2.2, Definitions 3–5, proof of Theorem 2, (10), §4.1.7, §4.2, (35)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory

namespace UniversalBarrier.NSC

/-- **Proper convex domain** (§2.1, p. 2; footnote 1, p. 1): a convex set `K ⊆ ℝⁿ` with
non-empty interior that contains no 1-dimensional affine subspace (no line `{x + t v : t ∈ ℝ}`
with `v ≠ 0`). `K` is not assumed closed or bounded. -/
def IsProperConvexDomain {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ (interior K).Nonempty ∧
    ∀ x v : EuclideanSpace ℝ (Fin n), (∀ t : ℝ, x + t • v ∈ K) → v = 0

/-- The **polar set of `K` with respect to `x`** (Definition 3, p. 3):
`K◦(x) = {y ∈ ℝⁿ : yᵀ(z − x) ≤ 1 for all z ∈ K}`. -/
def polarAt {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ z ∈ K, ⟪y, z - x⟫ ≤ 1}

/-- The **universal barrier** of `K` (Definition 3, p. 3): `φ(x) = log Volₙ(K◦(x))`.
The paper defines it on `int(K)` only; off `int(K)` this total function carries a junk value
(`Volₙ(K◦(x))` may be `∞`, whose `toReal` is `0`, and `log 0 = 0`). -/
noncomputable def universalBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log (volume (polarAt K x)).toReal

/-- The **marginal distribution `p(L, h; ·)` of `L` along `h`** (Definition 4, p. 3): the density of
`yᵀh` for `y` uniform on `L`. The `(n−1)`-dimensional measure of the slice `{y ∈ L : yᵀh = t}`
(the published `sectionVol`, an unnormalized Hausdorff measure) is divided by its own integral
over `t`, which makes it a probability density for every `h ≠ 0`; the printed normalization
`Volₙ(L)` is the right one only for unit `h`. -/
noncomputable def marginalDensity {n : ℕ} (L : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  EntropicBarrier.Universal.sectionVol L h t / ∫ s, EntropicBarrier.Universal.sectionVol L h s

/-- The mean `μ₁(p) = ∫ t p(t) dt` of a density `p` on `ℝ` (§2.2, p. 3). -/
noncomputable def mu1 (p : ℝ → ℝ) : ℝ := ∫ t, t * p t

/-- The variance `μ₂²(p) = ∫ (t − μ₁(p))² p(t) dt` (§2.2, p. 3). -/
noncomputable def mu2sq (p : ℝ → ℝ) : ℝ := ∫ t, (t - mu1 p) ^ 2 * p t

/-- The third central moment `μ₃³(p) = ∫ (t − μ₁(p))³ p(t) dt` (§2.2, p. 3). -/
noncomputable def mu3cube (p : ℝ → ℝ) : ℝ := ∫ t, (t - mu1 p) ^ 3 * p t

/-- `p` is **`1/m`-concave** (Definition 5, p. 4, with `s = 1/m`; `m = 0` is `s = +∞`), with
`t₁, t₂` ranging over the support points `{p > 0}`: for `θ ∈ [0, 1]`,
`p(θ t₁ + (1 − θ) t₂) ≥ (θ p(t₁)^{1/m} + (1 − θ) p(t₂)^{1/m})^m` if `m ≥ 1`, and
`p(θ t₁ + (1 − θ) t₂) ≥ max{p(t₁), p(t₂)}` if `m = 0`. -/
def IsOneOverMConcave (m : ℕ) (p : ℝ → ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, 0 < p t₁ → 0 < p t₂ → ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    (if m = 0 then max (p t₁) (p t₂)
     else (θ * p t₁ ^ ((1 : ℝ) / m) + (1 - θ) * p t₂ ^ ((1 : ℝ) / m)) ^ (m : ℝ))
      ≤ p (θ * t₁ + (1 - θ) * t₂)

/-- The **`1/(k−1)`-affine distributions** `𝒬` ((10), p. 7):
`q(t) = (αt + β)^{k−1} 1_{[a,b]}(t) / ∫_a^b (αu + β)^{k−1} du` with `αt + β ≥ 0` on `[a, b]`,
restricted to the non-degenerate case `a < b` with a positive normalizing integral. -/
def IsKAffine (k : ℕ) (q : ℝ → ℝ) : Prop :=
  ∃ a b α β : ℝ, a < b ∧ (∀ t ∈ Set.Icc a b, 0 ≤ α * t + β) ∧
    0 < ∫ u in a..b, (α * u + β) ^ (k - 1) ∧
    q = fun t => Set.indicator (Set.Icc a b) (fun u => (α * u + β) ^ (k - 1)) t /
                   ∫ u in a..b, (α * u + β) ^ (k - 1)

/-- `Ξ(p) = |μ₃³(p) / μ₂³(p)|` (§4.2, p. 13), with `μ₂³(p) = (μ₂²(p))^{3/2}`. -/
noncomputable def Xi (p : ℝ → ℝ) : ℝ := |mu3cube p / Real.sqrt (mu2sq p) ^ 3|

/-- `f₀(γ)` (§4.1.7, p. 12), the defining (unsimplified) display:
`k(γᵏ−1)[k(k+1)(γ^{k+2}−1) − 2k(k+2)(γ^{k+1}−1) + (k+1)(k+2)(γᵏ−1)]
 − (k+1)[k(γ^{k+1}−1) − (k+1)(γᵏ−1)]²`. -/
noncomputable def f0 (k : ℕ) (γ : ℝ) : ℝ :=
  (k : ℝ) * (γ ^ k - 1) *
      ((k : ℝ) * ((k : ℝ) + 1) * (γ ^ (k + 2) - 1)
        - 2 * (k : ℝ) * ((k : ℝ) + 2) * (γ ^ (k + 1) - 1)
        + ((k : ℝ) + 1) * ((k : ℝ) + 2) * (γ ^ k - 1))
    - ((k : ℝ) + 1) * ((k : ℝ) * (γ ^ (k + 1) - 1) - ((k : ℝ) + 1) * (γ ^ k - 1)) ^ 2

/-- `g(γ, k)` ((35), p. 17). -/
noncomputable def gpoly (k : ℕ) (γ : ℝ) : ℝ :=
  4 * ((k : ℝ) - 1) ^ 2 *
      (((k : ℝ) + 1) ^ 2 * (γ ^ k - 1) * (γ ^ (k + 2) - 1)
        - (k : ℝ) * ((k : ℝ) + 2) * (γ ^ (k + 1) - 1) ^ 2) ^ 3
    - (2 * (k : ℝ) ^ 2 * ((k : ℝ) + 2) * ((k : ℝ) + 3) * (γ ^ (k + 1) - 1) ^ 3
        + ((k : ℝ) + 2) * ((k : ℝ) + 1) ^ 3 * (γ ^ k - 1) ^ 2 * (γ ^ (k + 3) - 1)
        - 3 * (k : ℝ) * ((k : ℝ) + 3) * ((k : ℝ) + 1) ^ 2 * (γ ^ k - 1) * (γ ^ (k + 1) - 1)
            * (γ ^ (k + 2) - 1)) ^ 2

/-- `c_n = (n − 1)/(2√n)` (proof of Theorem 2, p. 5). -/
noncomputable def cn (n : ℕ) : ℝ := ((n : ℝ) - 1) / (2 * Real.sqrt n)

/-- `ℓ(t) = (2t³ + 6t + 4c_n)/(1 + t²)^{3/2}` (proof of Theorem 2, p. 5). -/
noncomputable def ell (n : ℕ) (t : ℝ) : ℝ :=
  (2 * t ^ 3 + 6 * t + 4 * cn n) / (1 + t ^ 2) ^ ((3 : ℝ) / 2)

end UniversalBarrier.NSC


