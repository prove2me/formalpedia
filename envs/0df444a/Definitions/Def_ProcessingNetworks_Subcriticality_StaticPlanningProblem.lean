-- Prove2me | Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
-- name    : ProcessingNetworks_Subcriticality_StaticPlanningProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:24:09.344068+00:00
-- url     : https://prove2.me/theorems/05c688c4-f7a1-4f61-bfa0-cef12961e385
-- title:
--   The static planning problem, the subcritical region, and their augmented variant
-- statement:
--   Given `SPNPlanningData` $(B, \Gamma, m, A, b)$ (hence $R := (B-\Gamma)M^{-1}$), the **static
--   planning problem (SPP)**, Eqs. (5.5)-(5.8), is the linear program in $(x, \gamma) \in
--   \mathbb{R}_+^J \times \mathbb{R}$
--   $$
--   \min \gamma \quad \text{s.t.} \quad Rx = \lambda, \quad Ax \le \gamma b, \quad x \ge 0.
--   $$
--   `SPPFeasible D γ lam x` asserts that $x$ is feasible at level $\gamma$ for arrival-rate vector
--   $\lambda$; `IsOptimalSPPValue D lam γstar` asserts $\gamma^\ast$ is the SPP's optimal value
--   (the least feasible $\gamma$, i.e. the least element — not merely a lower bound — of the set of
--   feasible $\gamma$'s). The SPN is **subcritical** for $\lambda$ exactly when $\gamma^\ast(\lambda)
--   < 1$; the **subcritical region**
--   $$
--   \Lambda := \{\lambda \in \mathbb{R}_+^I : \gamma^\ast(\lambda) < 1\}
--   $$
--   is `SubcriticalRegion D`, Eq. (5.16).
--
--   For an SPN with **alternate routing and immediate commitment** (Section 4.2), arrivals from $L$
--   sources at rates $\nu_\ell$ must be routed, without delay, into buffers eligible under a
--   zero-one matrix $G$ ($G_{\ell i} = 1$ iff source $\ell$ may route into buffer $i$). The decision
--   variables of the SPP are then augmented to include the routing matrix $\varphi \in
--   \mathbb{R}_+^{L\times I}$, subject to
--   $$
--   \varphi_{\ell i} = 0 \text{ if } G_{\ell i} = 0, \qquad \sum_{i} \varphi_{\ell i} = \nu_\ell,
--   \qquad Rx = \lambda := \Bigl(\sum_\ell \varphi_{\ell i}\Bigr)_i, \qquad Ax \le \gamma b, \quad
--   x,\varphi \ge 0,
--   $$
--   Eqs. (5.10), (5.11), (5.13)-(5.15) — `AugmentedSPPFeasible`, `IsOptimalAugmentedSPPValue`, and
--   `IsAugmentedSubcritical` (the augmented analogue of $\gamma^\ast < 1$) formalize this variant.
--
--   **Formalization note.** `IsOptimalSPPValue`/`IsOptimalAugmentedSPPValue` use Mathlib's `IsLeast`
--   (membership in the feasible set *and* being a lower bound of it), matching the book's implicit
--   assumption that the SPP's infimum is attained — the book writes "$\gamma^\ast \le 1$ iff there
--   exists $x$" rather than an approximate statement, which presupposes attainment. The subcritical
--   region is a set of **nonnegative** arrival-rate vectors, $\Lambda \subset \mathbb{R}^I_+$, exactly
--   as (5.16) writes it, and the augmented problem requires $\varphi \ge 0$ as well as $x \ge 0$,
--   exactly as (5.15) writes it.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 93-99, Eqs. (5.5)-(5.8), (5.10)-(5.16)

import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData

namespace ProcessingNetworks.Subcriticality

/-- Feasibility of the static planning problem (SPP) at level `γ` for arrival-rate vector `λ`,
Eqs. (5.5)-(5.8), p. 93 (PDF p. 109): `x` is a nonnegative activity-rate vector satisfying the
material balance constraint `Rx = λ` (5.6) and the capacity constraint `Ax ≤ γb` (5.7)-(5.8). -/
def SPPFeasible {I J K : ℕ} (D : SPNPlanningData I J K) (γ : ℝ) (lam : Fin I → ℝ)
    (x : Fin J → ℝ) : Prop :=
  D.R.mulVec x = lam ∧ (∀ j, 0 ≤ x j) ∧ ∀ k, (D.A.mulVec x) k ≤ γ * D.b k

/-- `γ*` is the optimal objective value of the SPP for arrival-rate vector `λ`: the least `γ` for
which the SPP (5.5)-(5.8) is feasible. -/
def IsOptimalSPPValue {I J K : ℕ} (D : SPNPlanningData I J K) (lam : Fin I → ℝ)
    (γstar : ℝ) : Prop :=
  IsLeast {γ : ℝ | ∃ x, SPPFeasible D γ lam x} γstar

/-- The subcritical region `Λ`, Eq. (5.16), p. 94 (PDF p. 110): nonnegative arrival-rate vectors
`λ ∈ ℝ^I_+` for which the SPP's optimal objective value is strictly less than `1`. -/
def SubcriticalRegion {I J K : ℕ} (D : SPNPlanningData I J K) : Set (Fin I → ℝ) :=
  {lam | (∀ i, 0 ≤ lam i) ∧ ∃ γstar, IsOptimalSPPValue D lam γstar ∧ γstar < 1}

/-- Feasibility of the augmented static planning problem for alternate routing with immediate
commitment, Eqs. (5.10), (5.11), (5.13)-(5.15), p. 99 (PDF p. 115): the decision variables are
extended to include the `L × I` routing matrix `φ` (`φ ℓ i = 0` whenever routing option `G ℓ i`
is unavailable, and `φ`'s row sums match the source arrival rates `ν`), with `λ` derived from `φ`
via (5.11) and folded into the ordinary SPP constraints (5.13)-(5.15), `φ, x ≥ 0` (5.15). -/
def AugmentedSPPFeasible {I J K L : ℕ} (D : SPNPlanningData I J K) (G : Matrix (Fin L) (Fin I) ℝ)
    (γ : ℝ) (nu : Fin L → ℝ) (phi : Fin L → Fin I → ℝ) (x : Fin J → ℝ) : Prop :=
  (∀ ℓ i, G ℓ i = 0 → phi ℓ i = 0) ∧ (∀ ℓ, ∑ i, phi ℓ i = nu ℓ) ∧
  D.R.mulVec x = (fun i => ∑ ℓ, phi ℓ i) ∧ (∀ ℓ i, 0 ≤ phi ℓ i) ∧ (∀ j, 0 ≤ x j) ∧
  ∀ k, (D.A.mulVec x) k ≤ γ * D.b k

/-- Optimal objective value of the augmented SPP, for a given source-rate vector `ν`. -/
def IsOptimalAugmentedSPPValue {I J K L : ℕ} (D : SPNPlanningData I J K)
    (G : Matrix (Fin L) (Fin I) ℝ) (nu : Fin L → ℝ) (γstar : ℝ) : Prop :=
  IsLeast {γ : ℝ | ∃ phi x, AugmentedSPPFeasible D G γ nu phi x} γstar

/-- Subcriticality for the alternate-routing model, "as that term was defined in the last
paragraph of Section 5.2" (p. 99, PDF p. 115): the augmented SPP's optimal objective value is
strictly less than `1`. -/
def IsAugmentedSubcritical {I J K L : ℕ} (D : SPNPlanningData I J K)
    (G : Matrix (Fin L) (Fin I) ℝ) (nu : Fin L → ℝ) : Prop :=
  ∃ γstar, IsOptimalAugmentedSPPValue D G nu γstar ∧ γstar < 1

end ProcessingNetworks.Subcriticality


