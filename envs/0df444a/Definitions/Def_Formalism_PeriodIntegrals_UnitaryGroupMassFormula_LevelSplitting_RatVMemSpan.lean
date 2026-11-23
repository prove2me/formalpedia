-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:21.260187+00:00
-- url     : https://prove2.me/theorems/3456ff5a-ce7e-4f7b-b223-e84fd272bd41
-- title:
--   Rat VMem Span
-- statement:
--   Definitions and structural lemmas for Rat VMem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
def covR (x : Fin n → E) : Fin n → R ⊗[F] E := fun j => inclR R (∑ i, σ (x i) * J i j)
variable {R σ J}
end Gen
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom
end Loc
end PI.LevelKSplit.W.Glob


