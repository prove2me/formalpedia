-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:53.961795+00:00
-- url     : https://prove2.me/theorems/cddc5344-db3f-4401-ab56-873027315ab4
-- title:
--   Inst Compact UG
-- statement:
--   Definitions and structural lemmas for Inst Compact UG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/InstCompactUG.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
abbrev UG (N : ℕ) := ↥(Matrix.unitaryGroup (Fin N) ℂ)
lemma isCompact_UG (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hc : IsClosed ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
    have : ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) =
        {g | star g * g = 1} ∩ {g | g * star g = 1} := by
      ext g; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  have hb : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      Set.pi Set.univ fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hb.of_isClosed_subset hc ?_
  intro g hg i _ j _
  simpa using entry_norm_bound_of_unitary hg i j
instance instCompactUG (N : ℕ) : CompactSpace (UG N) :=
  isCompact_iff_compactSpace.mp (isCompact_UG N)
instance instMeasUG (N : ℕ) : MeasurableSpace (UG N) := borel _
instance instBorelUG (N : ℕ) : BorelSpace (UG N) := ⟨rfl⟩
def ent {N : ℕ} (g : UG N) : Fin N × Fin N → ℂ := fun ij => (g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2
def IsPD {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
    ∀ g : UG N, f g * (g : Matrix (Fin N) (Fin N) ℂ).det ^ k = MvPolynomial.eval (ent g) P
def detP (N : ℕ) : MvPolynomial (Fin N × Fin N) ℂ := (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det
def coordC {N : ℕ} (i j : Fin N) : C(UG N, ℂ) :=
  ⟨fun g => (g : Matrix (Fin N) (Fin N) ℂ) i j,
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)⟩
def algA (N : ℕ) : StarSubalgebra ℂ C(UG N, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)
def Sep {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → UG N → ℂ), (∀ i, IsPD (a i)) ∧ (∀ i, Continuous (b i)) ∧
    ∀ h y : UG N, f (h⁻¹ * y) = ∑ i, a i h * b i y
end PI.UnitaryGroupMassFormula.PolyCoef


