-- Prove2me | Definitions.Def_WassTwoStage_LP1_Supplement_PNorm
-- name    : WassTwoStage_LP1_Supplement_PNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:01:18.716433+00:00
-- url     : https://prove2.me/theorems/7e795dd8-72c1-4370-af61-02f9daedc27e
-- title:
--   The $p$-norm reference distance, its 1-Wasserstein ball, the worst-case expectation and the value of problem (1)
-- statement:
--   Fix an exponent $p\in[1,\infty]$. The **$p$-norm** of $\xi\in\mathbb R^K$ is
--
--   $$\|\xi\|_p=\Big(\sum_{k\in[K]}|\xi_k|^p\Big)^{1/p}\quad(p<\infty),\qquad \|\xi\|_\infty=\max_{k\in[K]}|\xi_k|,$$
--
--   and the **reference distance** of Theorem 7 is $d(\xi_1,\xi_2)=\|\xi_1-\xi_2\|_p$.
--
--   Take the data of the two-stage problem of Section 4 with $Q=0$ (the published setting `WassTwoStage.LP1.Setting`): a first-stage cost $c$ and feasible set $\mathcal X\subseteq\mathbb R^{N_1}$, a recourse cost $q\in\mathbb R^{N_2}$, affine maps $T(x)\in\mathbb R^{M\times K}$ and $h(x)\in\mathbb R^M$, a recourse matrix $W$, samples $\hat\xi_1,\dots,\hat\xi_I\in\mathbb R^K$ and a radius $\epsilon$. The recourse value is $Z(x,\xi)=\inf\{q^\top y: T(x)\xi+h(x)\le Wy\}\in[-\infty,+\infty]$.
--
--   1. The **1-Wasserstein ball** $\mathcal B^1_\epsilon(\hat{\mathbb P}_I)$ (Definition 3 with $r=1$ and $\Xi=\mathbb R^K$) is the set of probability measures $\mathbb P$ on $\mathbb R^K$ whose optimal transport cost to $\hat{\mathbb P}_I=\frac1I\sum_{i\in[I]}\delta_{\hat\xi_i}$ for the cost $\|\xi-\xi'\|_p$ is at most $\epsilon$; couplings have first marginal $\mathbb P$ and second marginal $\hat{\mathbb P}_I$.
--   2. The **worst-case expectation** (2) is
--   $$\mathcal Z_p(x)=\sup_{\mathbb P\in\mathcal B^1_\epsilon(\hat{\mathbb P}_I)}\mathbb E_{\mathbb P}\big[Z(x,\tilde\xi)\big].$$
--   3. The **optimal value of problem (1)** is $\inf_{x\in\mathcal X}\, c^\top x+\mathcal Z_p(x)$.
--
--   These are the objects whose value Theorem 7 shows to be NP-hard to compute. They differ from the published Section 4 objects only in the reference distance: the gauge (31) is replaced by the $p$-norm.
--
--   **Formalization Note** All values are extended reals. The expectation of the extended-real recourse value is `erealExpectation`: it is $+\infty$ when the positive part has infinite integral, so no measure is dropped for being non-integrable. The finite-first-moment condition $\mathbb P\in\mathcal M^1(\mathbb R^K)$ of Definition 3 is not written separately: a finite transport cost to the finitely supported $\hat{\mathbb P}_I$ implies it. The weights $w_\pm$ of the published structure are not used. The maximum in $\|\cdot\|_\infty$ is a real supremum over the finite set $[K]$; it is $0$ for $K=0$.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, pp. 5–6, (1)–(3), Definition 3; p. 25, Theorem 7 (reference distance ‖ξ1 − ξ2‖p)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassTwoStage_LP1_Setting

open MeasureTheory Matrix

namespace WassTwoStage.LP1.Supplement

/-- The `p`-norm on `ℝ^K` for an exponent `p ∈ [1, ∞]` (Hanasusanto–Kuhn, arXiv:1609.07505v3,
§4.2, p. 25, Theorem 7 and its proof): `‖ξ‖_p = (Σ_k |ξ_k|^p)^{1/p}` for finite `p` and
`‖ξ‖_∞ = max_k |ξ_k|`. The maximum over the finite index set `Fin K` is the real `⨆`, which is `0`
for `K = 0` (the norm of the empty vector). The value at exponents `p < 1` is never used. -/
noncomputable def pNorm (p : ENNReal) {K : ℕ} (ξ : Fin K → ℝ) : ℝ :=
  if p = ⊤ then ⨆ k, |ξ k| else (∑ k, |ξ k| ^ p.toReal) ^ (1 / p.toReal)

/-- The reference distance of Theorem 7 (p. 25), `d(ξ₁, ξ₂) = ‖ξ₁ − ξ₂‖_p`, as an `ℝ≥0∞`-valued
transport cost. -/
noncomputable def pCost (p : ENNReal) {K : ℕ} (ξ ξ' : Fin K → ℝ) : ENNReal :=
  ENNReal.ofReal (pNorm p (ξ - ξ'))

variable {K M N₁ N₂ I : ℕ}

/-- The 1-Wasserstein ball `B¹_ε(ℙ̂_I)` of Definition 3 (p. 6) with `r = 1`, `Ξ = ℝ^K` and the
reference distance `d(ξ₁, ξ₂) = ‖ξ₁ − ξ₂‖_p` of Theorem 7 (p. 25): the probability measures `ℙ` on
`ℝ^K` whose optimal transport cost to the empirical distribution `ℙ̂_I = (1/I) Σ_i δ_{ξ̂_i}`, for the
cost `‖ξ − ξ'‖_p`, is at most `ε`. The coupling has first marginal `ℙ` and second marginal `ℙ̂_I`.
The scaling parameters `w₊, w₋` of the structure `Data` (the gauge (31)) are not used. -/
def ballP (p : ENNReal) (d : Data K M N₁ N₂ I) : Set (Measure (Fin K → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    RWPI.SqrtLasso.transportCost (pCost p) P
      (WassersteinDRO.Duality.empiricalDistribution d.ξhat) ≤ ENNReal.ofReal d.ε}

/-- The worst-case expectation (2), p. 5, over the `p`-norm 1-Wasserstein ball:
`𝒵_p(x) = sup_{ℙ ∈ B¹_ε(ℙ̂_I)} E_ℙ[Z(x, ξ̃)]`, with the recourse function `Z(x, ξ)` of (3) for
`Q = 0` (`Data.recourse`). The expectation of the extended-real recourse value is `+∞` whenever its
positive part has infinite integral. -/
noncomputable def worstCaseP (p : ENNReal) (d : Data K M N₁ N₂ I) (x : Fin N₁ → ℝ) : EReal :=
  ⨆ (P : Measure (Fin K → ℝ)) (_ : P ∈ ballP p d),
    WassersteinDRO.Duality.erealExpectation P (fun ξ => d.recourse x ξ)

/-- The optimal value of the two-stage distributionally robust problem (1), p. 5, when the
ambiguity set is the `p`-norm 1-Wasserstein ball: `inf {cᵀx + 𝒵_p(x) : x ∈ X}`. -/
noncomputable def valueP (p : ENNReal) (d : Data K M N₁ N₂ I) : EReal :=
  ⨅ x ∈ d.X, ((d.c ⬝ᵥ x : ℝ) : EReal) + worstCaseP p d x

end WassTwoStage.LP1.Supplement


