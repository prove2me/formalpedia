-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:42.109795+00:00
-- url     : https://prove2.me/theorems/b6790b2c-9e7a-4a8d-8770-f43a3264bfaa
-- title:
--   Eq Id Of Fixes Torsion
-- statement:
--   Definitions and structural lemmas for Eq Id Of Fixes Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
section Twist
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))
def twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb L (K := K × Fin 2) (fun p => φ p.1 ≫ ![σ, 𝟙 X] p.2) (fun p => -ε p.1 * ![1, -1] p.2)) where
  s := fun j => ∏ k : K,
    res ((fun _ hy => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (k, b)) :
        LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j ≤
          LB.wchart L (fun b => φ k ≫ ![σ, 𝟙 X] b) (fun b => j (k, b)))
      ((LB.pullGen L _ _ c (φ k)).s (fun b => j (k, b))) ^ (-ε k)
end Twist
section Embed
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
end Embed
section Theta
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
def secVal {k : ℤ} (s : LB.Sec (LPow A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s r z J
def thetaVal {k : ℤ} {x : T ⟶ A} (t : LB.Gen (thetaLB A L k x)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (translPt A x).left]) (ε := ![k, -k]) t r z J
def negVal {k : ℤ} (t : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) t r z J
variable (σ : A ⟶ A) (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
variable [IsMonHom σ]
end Theta
section Assemble
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (σ : A ⟶ A)
  (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))
end Assemble
end GlobalTheory.TorsionFixedAut


