-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:17.947076+00:00
-- url     : https://prove2.me/theorems/53a6a3ba-9176-49c1-84fb-1384980fa024
-- title:
--   Is Inv Der
-- statement:
--   Definitions and structural lemmas for Is Inv Der, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/IsInvDer.lean

import Mathlib
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
noncomputable section
namespace GlobalTheory.KS
open Classical in

def rsT {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : Γ(Y, O) := if h : O ≤ O₀ then resG Y h s else 0
open Classical in

def pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : Γ(Z, O) :=
  if h : O ≤ f ⁻¹ᵁ O₀ then (f.appLE O₀ O h).hom s else 0
variable {K : Type} [Field K] {Y X : Scheme.{0}} {I : Type} {g : ℕ}
abbrev C1 (U : I → Y.Opens) : Type := ∀ i j, Γ(Y, U i ⊓ U j)
def IsCoc (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∀ i j k, rsT (c i j) (U i ⊓ U j ⊓ U k) + rsT (c j k) (U i ⊓ U j ⊓ U k) = rsT (c i k) (U i ⊓ U j ⊓ U k)
def IsCob (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∃ b : ∀ i, Γ(Y, U i), ∀ i j, c i j = rsT (b j) (U i ⊓ U j) - rsT (b i) (U i ⊓ U j)
def Cohom (f : Y ⟶ Y) (U : I → Y.Opens) (c c' : C1 U) : Prop :=
  ∃ b : ∀ i k, Γ(Y, U i ⊓ f ⁻¹ᵁ U k),
    (∀ i i' k, rsT (b i' k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) - rsT (b i k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) =
      rsT (c i i') (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k)) ∧
    ∀ i k k', rsT (b i k) (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') - rsT (b i k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') =
      pbT f (c' k k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k')
def lc (q : Y ⟶ Sp K) {U : I → Y.Opens} (c : Fin g → K) (φ : Fin g → C1 U) : C1 U :=
  fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j
def IsDerK {R : Type} [CommRing R] (x₀ : R →+* K) (D : R → K) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a
structure LocDerK {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W')
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
def IsInvDer {A₀ : Over (Sp K)} [GrpObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ W : A₀.left.Opens, Γ(A₀.left, W) → Γ(A₀.left, W)) : Prop :=
  ∀ (W : A₀.left.Opens) (f : Γ(A₀.left, W)),
    pbT ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) =
      pbT (snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) +
        constFn (R := DualNumber K) (fst (epsR K) A₀).left _ DualNumber.eps *
          pbT (snd (epsR K) A₀).left (dd W f) ((snd (epsR K) A₀).left ⁻¹ᵁ W)
structure KSCoc {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W : I → X.Opens)
    (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O))
    (θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)) : Prop where
  der : ∀ i, LocDerK q p m D (W i) (d i)
  diff : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, d j O f - d i O f = ∑ a, rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
def IsDlog (m : Y ⟶ X) (L : LB X) (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O))
    (φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)) : Prop :=
  ∀ a i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ a i j = dd a _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))
def IsConstK (A' : Over (Sp (DualNumber K))) [GrpObj A'] (A₀ : Over (Sp K)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap K (DualNumber K))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end


