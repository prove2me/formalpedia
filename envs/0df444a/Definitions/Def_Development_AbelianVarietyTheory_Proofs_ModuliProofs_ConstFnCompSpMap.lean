-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:50.837625+00:00
-- url     : https://prove2.me/theorems/4062563c-415b-41ba-8977-54d6ee9e179a
-- title:
--   Const Fn Comp Sp Map
-- statement:
--   Definitions and structural lemmas for Const Fn Comp Sp Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
def Der (h : Z ⟶ X) (T : Z.Opens) (δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')) : Prop :=
  (∀ O f f' O', O' ≤ T → O' ≤ h ⁻¹ᵁ O → δ O (f * f') O' = pbT h f O' * δ O f' O' + pbT h f' O' * δ O f O') ∧
  (∀ O O₁ (f : Γ(X, O)) O', O₁ ≤ O → O' ≤ T → O' ≤ h ⁻¹ᵁ O₁ → δ O₁ (rsT f O₁) O' = δ O f O') ∧
  ∀ O f O' O'', O'' ≤ O' → O' ≤ T → O' ≤ h ⁻¹ᵁ O → rsT (δ O f O') O'' = δ O f O''
def dl (h : Z ⟶ X) (L : LB X) (δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')) (a b : L.ι) (O' : Z.Opens) :
    Γ(Z, O') := δ _ (L.g a b).val O' * pbT h (L.g a b).inv O'
def tr (p : Z ⟶ Y) (m : Y ⟶ X₂) (π : X₂ ⟶ X) (W : X₂.Opens) (d : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Y, m ⁻¹ᵁ O))
    (O : X.Opens) (f : Γ(X, O)) (O' : Z.Opens) : Γ(Z, O') :=
  pbT p (d (π ⁻¹ᵁ O ⊓ W) (pbT π f _)) O'
variable {K R : Type} [Field K] [CommRing R]
def IsVF (q : Z ⟶ Sp K) (w : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) : Prop :=
  (∀ W f f', w W (f + f') = w W f + w W f') ∧ (∀ W f f', w W (f * f') = f * w W f' + f' * w W f) ∧
    (∀ W W' (f : Γ(Z, W)), W' ≤ W → w W' (rsT f W') = rsT (w W f) W') ∧ ∀ W a, w W (constFn q W a) = 0
end GlobalTheory.KS.Sym
end


