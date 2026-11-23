-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:13.640798+00:00
-- url     : https://prove2.me/theorems/eb1152a4-6dd7-43e7-966d-b068f94b60a8
-- title:
--   Loc Dens HH
-- statement:
--   Definitions and structural lemmas for Loc Dens HH, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
section Mat
variable {A : Type} [CommRing A] (s : A →+* A)
end Mat
section Int
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
def intA (z : Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F
variable {b v}
def GoodV (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) : Prop :=
  (∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ m, algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F) ∧
  (∀ i j m, algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F)
end Int
end PI.VolStabW


