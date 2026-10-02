-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
-- name    : ProcessingNetworks_ProportionalFairness_FluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:16:13.539896+00:00
-- url     : https://prove2.me/theorems/3f768ed6-6eaa-4571-8845-c8656f02b233
-- title:
--   The PF fluid model for a unitary network (Definition 10.3, Eqs. 10.29-10.35)
-- statement:
--   **Definition 10.3.** The PF fluid model consists of Eqs. (10.29)-(10.35): the usual balance
--   equation $Z=Z(0)+A-D$, nonnegativity, $A(t)=\lambda t+P'D(t)$, $D=M^{-1}T$, $T$ nondecreasing
--   and globally Lipschitz with $T(0)=0$, and, for each $i$ in demand group $\ell$,
--   $$Z_i(t)>0 \implies \dot T_i(t) = \tilde\psi_\ell(Y(t))\frac{Z_i(t)}{Y_\ell(t)},\qquad Y(t) :=
--   GZ(t).$$
--   `PFFluidStable` specializes Definition 6.3 (mission III) to this fluid model.
--
--   **Formalization note.** `IsTotalArrivalRates` (Eq. 2.38) and `RegularPoint` (Definition 8.7)
--   are restated locally, matching this series' convention. `Th`'s global Lipschitz property
--   (10.33) is stated with an explicit witness constant, per the book's own remark that it follows
--   from the dropped equation (6.6). (10.34) is stated as the conclusion of Theorem 7.8 that it
--   recapitulates: whenever $Z_i(t) > 0$, the derivative $\dot T_i(t)$ *exists* and equals
--   $\tilde\psi_\ell(Y(t)) Z_i(t)/Y_\ell(t)$ (`HasDerivAt`), not merely "equals it if it exists" —
--   this is what the book uses to conclude that $\dot D_i(t)$ in the entropy function (10.38) exists
--   and is positive whenever $Z_i(t) > 0$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 194-196, Section 10.4, Eqs. (10.26),(10.29)-(10.35), Definition 10.3

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness

/-- The data of a unitary network operating under PF control (Section 10.4): `I`-vectors `lam`
(external arrival rates) and `m` (mean service times, `> 0`), an `I × I` routing matrix `P`, a
demand-group assignment `grp : Fin I → Fin L` (the partition `{I(ℓ), ℓ ∈ L}` of Section 10.3), and
the reduced allocation set `TildeAllocSet ⊂ ℝ^L_+` (Eq. 10.27) that the aggregate PF allocation
function `ψ̃` (Eq. 10.23) is built from. -/
structure PFUnitaryNetworkData (I L : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  P : Matrix (Fin I) (Fin I) ℝ
  grp : Fin I → Fin L
  TildeAllocSet : Set (Fin L → ℝ)

/-- The total-arrival-rate vector `α` (Eq. 2.38, restated): the fixed point `α = λ + P'α`. -/
def IsTotalArrivalRates {I L : ℕ} (dat : PFUnitaryNetworkData I L) (alpha : Fin I → ℝ) : Prop :=
  alpha = fun i => dat.lam i + ∑ k, dat.P k i * alpha k

/-- A point `t > 0` is regular for a fluid model solution `(A,D,T,Z)` if all four components are
differentiable at `t` (Definition 8.7, restated as in prior missions). -/
def RegularPoint {I : ℕ} (Ah Dh Th Zh : ℝ → Fin I → ℝ) (t : ℝ) : Prop :=
  DifferentiableAt ℝ Ah t ∧ DifferentiableAt ℝ Dh t ∧ DifferentiableAt ℝ Th t ∧
    DifferentiableAt ℝ Zh t

/-- Definition 10.3, Dai & Harrison p. 196 (PDF p. 212): the PF fluid model, Eqs. (10.29)-(10.35),
for a unitary network operating under the PF control policy. `Th` is required globally Lipschitz
via an explicit constant, per (10.33)'s own remark that (6.6) implies this. (10.34) says that
whenever `Zᵢ(t) > 0` the derivative `d/dt Tᵢ(t)` exists and equals `ψ̃_ℓ(Y(t)) Zᵢ(t)/Y_ℓ(t)` (the
conclusion of Theorem 7.8), which is what makes `Ḋᵢ(t)` in the entropy function (10.38) exist
and be positive whenever `Zᵢ(t) > 0`. -/
def IsPFFluidModelSolution {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Zh t = fun i => Zh 0 i + Ah t i - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Ah t i = dat.lam i * t + ∑ k, dat.P k i * Dh t k) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Th t i / dat.m i) ∧
  (Th 0 = 0 ∧ Monotone Th ∧
    ∃ Kc : ℝ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ i, |Th t i - Th s i| ≤ Kc * (t - s)) ∧
  (∀ t : ℝ, 0 < t → ∀ i, 0 < Zh t i →
    HasDerivAt (fun u => Th u i)
      (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i)) t)

/-- Definition 6.3 (fluid model stability, mission III), specialized to the PF fluid model. -/
def PFFluidStable {I L : ℕ} (dat : PFUnitaryNetworkData I L) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ),
    IsPFFluidModelSolution dat Ah Dh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.ProportionalFairness


