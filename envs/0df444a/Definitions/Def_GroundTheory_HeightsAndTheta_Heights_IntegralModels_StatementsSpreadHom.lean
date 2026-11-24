-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:01.545407+00:00
-- url     : https://prove2.me/theorems/cce5a2a8-a9dc-4ea5-95a0-eb444b2b03f0
-- title:
--   Statements Spread Hom
-- statement:
--   Definitions and structural lemmas for Statements Spread Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean

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
open CategoryTheory AlgebraicGeometry
noncomputable section
section PullbackHom
variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
def pullbackHomAlong (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G) :
    (Scheme.Modules.pullback k).obj F ⟶ (Scheme.Modules.pullback k).obj G :=
  (pullbackCompIso e (Iso.refl _)).hom ≫ (Scheme.Modules.pullback g).map ψ ≫
    (pullbackCompIso e (Iso.refl _)).inv
end PullbackHom
section Spread
def SpreadHom.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ = φ
def SpreadHomInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (hn : 0 < n), m ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G,
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₁ =
        pullbackHomAlong (toInvOpen_homOfLE f ℚ
          (isUnit_intCast_rat ((a : ℤ) * n) (by positivity))
          (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a n)) ψ₂ →
        ψ₁ = ψ₂
end Spread
end
end GroundTheory.Heights₂.Heights.Model


