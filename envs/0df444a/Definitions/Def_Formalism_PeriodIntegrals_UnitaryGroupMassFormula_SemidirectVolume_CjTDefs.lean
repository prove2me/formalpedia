-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:03.512823+00:00
-- url     : https://prove2.me/theorems/27ec760d-17c2-4874-a3b8-83391f05c152
-- title:
--   Cj TDefs
-- statement:
--   Definitions and structural lemmas for Cj TDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/CjTDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
def TraceBase : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E),
    Algebra.trace R (R ⊗[F] E) (hR R σ J (ratV (F := F) R x) (ratV (F := F) R y)) =
      algebraMap F R (Algebra.trace F E (hE σ J x y))
def TraceGramND : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (k : ℕ) (b : Module.Basis (Fin k) F (Fin M → E)),
      (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))).det ≠ 0
end PI.VolSemiDirect.W.Cj


