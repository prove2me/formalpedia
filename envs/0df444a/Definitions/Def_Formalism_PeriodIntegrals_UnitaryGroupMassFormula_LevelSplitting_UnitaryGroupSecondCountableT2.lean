-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:50.872818+00:00
-- url     : https://prove2.me/theorems/5b204a25-7647-424c-a9a2-8063b4c9a62e
-- title:
--   Unitary Group Second Countable T2
-- statement:
--   Definitions and structural lemmas for Unitary Group Second Countable T2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnitaryGroupSecondCountableT2.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
open Classical in

def projD (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    {m : ℕ} (Y D : Fin m → Fin n → E) (s : Set (Fin m)) (y : Fin n → R ⊗[F] E) :
    Fin n → R ⊗[F] E :=
  ∑ a, (if a ∈ s then covR R σ J (D a) ⬝ᵥ y else 0) • ratV (F := F) R (Y a)
def dualFrameAlt {r : ℕ} (P : Frame E n r) (T : F) : Fin (r + 1) → Fin n → E :=
  Fin.snoc P.f (algebraMap F E (-T)⁻¹ • P.z)
end Alg
section Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end Top
end PI.LevelKSplit.W.ExC


