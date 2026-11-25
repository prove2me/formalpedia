-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:03.014982+00:00
-- url     : https://prove2.me/theorems/c6f20dc9-74d6-453b-bc34-53a64fed3e12
-- title:
--   Orbit Push Cut
-- statement:
--   Definitions and structural lemmas for Orbit Push Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
def opBase (k r : ℕ) (T' : ℝ) : Fin (2 * r + k + 1) → ℂ := (Real.sqrt T' : ℂ) • wLast k r
def opCo (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : (Fin k → ℂ) × ℂ :=
  (fun i => v (wI k r (Fin.castSucc i)), v (wI k r (Fin.last k)))
def opOrb (k r : ℕ) (T' : ℝ) (x : Mt k r) : (Fin k → ℂ) × ℂ := opCo k r (Matrix.of x *ᵥ opBase k r T')
def opVec (k r : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val < r + k then p.1 ⟨i.val - r, by omega⟩
  else if i.val = r + k then p.2 else 0
def opAct (k r : ℕ) (s : Mat k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opCo k r (s *ᵥ opVec k r p)
def hypS (k : ℕ) (T' : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  {p | ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2 = -T'}
def hypPar (k : ℕ) (T' : ℝ) (q : EuclideanSpace ℂ (Fin k) × ℝ) : (Fin k → ℂ) × ℂ :=
  (fun i => q.1 i, (Real.sqrt (‖q.1‖ ^ 2 + T') : ℂ) * Complex.exp (q.2 * Complex.I))
def hypM (k : ℕ) (T' : ℝ) : Measure ((Fin k → ℂ) × ℂ) :=
  (1 / 2 : ℝ≥0∞) • (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).map (hypPar k T')
abbrev TrE (k : ℕ) := EuclideanSpace ℝ (Option (Fin k × Bool))
def opBeta (k : ℕ) (q : TrE k) (a : Fin k) : ℂ :=
  ((q (some (a, false)) : ℂ) + (q (some (a, true)) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)
def opGen (k r : ℕ) (q : TrE k) : Mat k r := fun i j =>
  if hi : r ≤ i.val ∧ i.val < r + k then (if j.val = r + k then opBeta k q ⟨i.val - r, by omega⟩ else 0)
  else if i.val = r + k then
    (if hj : r ≤ j.val ∧ j.val < r + k then star (opBeta k q ⟨j.val - r, by omega⟩)
     else if j.val = r + k then (q none : ℂ) * Complex.I else 0)
  else 0
def opE (k r : ℕ) (T' : ℝ) (ρ : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) '' Metric.ball 0 ρ
def tVol (k : ℕ) (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : TrE k) ρ)).toReal
def HypInv : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ s ∈ UWb k r, (hypM k T').map (opAct k r s) = hypM k T'
def OrbRepY : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ Q : Measure ((Fin k → ℂ) × ℂ), (∀ s ∈ UWb k r, Q.map (opAct k r s) = Q) → Q (hypS k T')ᶜ = 0 →
      (∀ C, IsCompact C → Q C < ⊤) → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ Q = c • νg.map (opOrb k r T')
def GaugeK : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νK : Measure (Mt k r), IsGaugeOn k r (UWset k r (wLast k r)) νK
def TubeLimK : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg νK : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    IsGaugeOn k r (UWset k r (wLast k r)) νK →
    Tendsto (fun ρ : ℝ => (νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0)
      (𝓝 (νK Set.univ).toReal)
def HypLocal : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    Tendsto (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0) (𝓝 (T' ^ k / 2 ^ (k + 1)))
def OpEMeas : Prop :=
  ∀ (k r : ℕ) (T' : ℝ) (ρ : ℝ), MeasurableSet (opE k r T' ρ)
def HypLF : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → hypM k T' (hypS k T')ᶜ = 0 ∧ ∀ C, IsCompact C → hypM k T' C < ⊤
end PI.RhsWLim.W


