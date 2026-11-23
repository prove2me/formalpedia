-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
-- name    : Formalism_PeriodIntegrals_LevelProdIdx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:28.900002+00:00
-- url     : https://prove2.me/theorems/1fd88205-7be3-49fe-b8d8-5be841515f7f
-- title:
--   Level Prod Idx
-- statement:
--   Definitions and structural lemmas for Level Prod Idx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LevelProdIdx.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI
open Formalism.UG in
def LevelProdIdx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ →
    (∀ x, x ∈ U ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) →
    (∀ v, Uloc v ≤ levelVL σ J v Lb) →
    {v | Uloc v ≠ levelVL σ J v Lb}.Finite →
    (∀ v, (Uloc v).relIndex (levelVL σ J v Lb) ≠ 0) →
    U ≤ levelAfL σ J Lb ∧ U.relIndex (levelAfL σ J Lb) ≠ 0
end PI


