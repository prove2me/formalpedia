-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:39.687846+00:00
-- url     : https://prove2.me/theorems/e6e87082-93ca-4a1d-adef-1f80a3429b42
-- title:
--   Statements Spread Local
-- statement:
--   Definitions and structural lemmas for Statements Spread Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
def SpreadsOn (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W : X.Opens) : Prop :=
  ∃ E' : (W : Scheme.{0}).Modules, IsVectorBundle E' ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E)
def SpreadLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (E : (baseChange f (ZLoc p)).Modules),
    IsVectorBundle E → ∀ x : baseChange f (ZLoc p),
      ∃ W : X.Opens, x ∈ baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W
def specZLocToBaseChange :
    Spec (CommRingCat.of (ZLoc ⟨2, Nat.prime_two⟩)) ⟶ baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (Int.castRingHom _))) (𝟙 _) (by simp)
end
end GroundTheory.Heights₂.Heights.Model


