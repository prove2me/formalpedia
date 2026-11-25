-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T15:01:30.469016+00:00
-- url     : https://prove2.me/theorems/bccd5d55-30b2-470e-9e01-9c67e08b88e7
-- title:
--   Psi Scal
-- statement:
--   Definitions and structural lemmas for Psi Scal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/PsiScal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
def kap0 {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x y : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  cubV c z J x y y⁻¹ * (val sym y.left z J)⁻¹ *
    val (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig T.hom z J ^ 2
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
abbrev cT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
def rigV (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk z)ˣ := val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig T.hom z J
def kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (x y : T ⟶ D.P.A) : (T.left.presheaf.stalk z)ˣ :=
  kap0 D.cub D.sym z J x y * cubV D.cub z J (cT D T a) (cT D T b) x * cubV D.cub z J (cT D T b) y y⁻¹ *
    (cubV D.cub z J (cT D T a) x y * cubV D.cub z J (cT D T b) x y⁻¹ * cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹
def PreU.AddG (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (r : R) {n : ℕ} (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ G) (z : T.left) (J), Good U.P.L.L z J →
    ∑ i, sval (σ i) (lift (toUnit T) x).left z J * sval (σ' i) (lift (toUnit T) y).left z J =
      gs (𝟙 _) z ⊤ (scal T.hom r) * (kap0 U.P.c U.P.sym z J x y).val *
        (sval θ (lift (toUnit T) (x * y)).left z J * sval θ (lift (toUnit T) (x * y⁻¹)).left z J)
def AddB (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D T₀ 2 α) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    (∀ a b α β : D.X, α = a + b → β = a - b →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
          (sval (f₀ a) (lift ρ (x * y)).left z J * sval (f₀ b) (lift ρ (x * y⁻¹)).left z J)) ∧
    ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) →
      ∑ i, sval (f i α) (lift ρ x).left z J * sval (f' i β) (lift ρ y).left z J = 0
def PreU.Theta (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) : Prop :=
  U.ExpT (𝟙_ _) 1 θ f ∧ ∃ j, θ.f j ≠ 0
def PsiRel (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (f : ∀ α, SecBT D T₀ 1 α) : Prop :=
  ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J),
    Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
      (val (D.psi χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J
def setPsi (D : DegPre R)
    (ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1))) (h : ∀ χ, (ψ χ).IsGen) :
    DegPre R := { D with psi := ψ, psi_gen := h }
def PsiScal (D : DegPre R)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ, (ga χ).IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (κ : T ⟶ TK R) (z : T.left) (J), Good D.P.L z J →
    (val (D.psi χ) κ.left z J).val = gs (𝟙 _) z ⊤ (scal κ.left (a χ).val) * (val (ga χ) (toUnit T).left z J).val
end
def AddA {S : Scheme.{0}} (P : PolAV S) (T₀ : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T₀)) {n : ℕ}
    (t t' : Fin n → LB.Sec (LPow P.A P.L ((2 : ℕ) : ℤ) T₀)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd T₀ (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd T₀ (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd T₀ (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1]), κ.IsGen ∧
    ∀ (T : Over S) (ρ : T ⟶ T₀) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      ∑ i, sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t i) (lift ρ x).left z J *
          sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((2 : ℕ) : ℤ)) (t' i) (lift ρ y).left z J =
        (val κ (lift ρ (lift x y)).left z J).val *
          (sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y)).left z J *
            sval (L := P.L) (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th (lift ρ (x * y⁻¹)).left z J)
abbrev EA {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) : Type :=
  SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L (k : ℤ) (Over.mk p))
abbrev WB {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (α : D.X) : Type :=
  SecMod (F := F) (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
end GlobalTheory.UU
end


