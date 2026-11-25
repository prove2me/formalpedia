-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:48.659429+00:00
-- url     : https://prove2.me/theorems/99d707a2-0a85-5927-9028-a61d129582ff
-- title:
--   Exists Unique Same Pt
-- statement:
--   Definitions and structural lemmas for Exists Unique Same Pt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

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
def AllPre (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegPre V}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G],
    PreU (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V)
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    (U : PreU (IsLocalRing.maximalIdeal V) D A G), p U
abbrev TA (V W : Type) [CommRing V] [CommRing W] [Algebra V W] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
abbrev Kbar (V : Type) [CommRing V] [IsDomain V] : Type := AlgebraicClosure (FractionRing V)
def FinExt (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W] : Prop :=
  Module.Finite V W ∧ Module.Free V W ∧ IsDomain W ∧ IsLocalHom (algebraMap V W) ∧
    IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W
theorem finExt_self (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    (h : IsAdicComplete (IsLocalRing.maximalIdeal V) V) : FinExt V V := by
  have hmap : (IsLocalRing.maximalIdeal V).map (algebraMap V V) = IsLocalRing.maximalIdeal V := by
    rw [show algebraMap V V = RingHom.id V from rfl, Ideal.map_id]
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [show algebraMap V V = RingHom.id V from rfl]
    infer_instance
  · rw [hmap]
    exact h
theorem CDVR.finExt_self {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDVR V) : FinExt V V :=
  GlobalTheory.UU.finExt_self V h.2.1
theorem cdvr_padicInt (p : ℕ) [Fact p.Prime] : CDVR ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance⟩
example (p : ℕ) [Fact p.Prime] : FinExt ℤ_[p] ℤ_[p] := (cdvr_padicInt p).finExt_self
example (p : ℕ) [Fact p.Prime] : ¬ FinExt ℤ_[p] ℚ_[p] := fun h => by
  have := h.2.2.2.1.map_nonunit (p : ℤ_[p]) (IsUnit.mk0 _ (by simpa using (Fact.out : p.Prime).ne_zero))
  exact PadicInt.irreducible_p.not_isUnit this
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def PreU.PullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (σ : U.SecGT T k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : Prop :=
  ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
    (rG : Z ⟶ (T ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
    rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) → rG ≫ (fst T G).left = rA ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left →
    ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
        sval σ rG z JG
def PullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))}
    (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) (s : Raw D F k) : Prop :=
  ∀ (α : D.X) (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
    sval (s α) (𝟙 _) z J = sval (f α) (φ ▷ D.P.A).left z J
def PreU.SamePt (U : PreU I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A)
    (y : TF (R := R) F ⟶ G) : Prop := x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = y.left
def PreU.Supp (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Prop :=
  ∃ t s, U.ExpF F k t s ∧ ∃ j, (s α).f j ≠ 0
def PreU.FE (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Prop :=
  ∀ t s, U.ExpF F k t s → DegPre.FamFE D F k s
def PreU.Acts (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (g : GtPtF D F)
    (x : TFK (R := R) F ⟶ A.A) : Prop :=
  x ^ k = 1 ∧ ∀ θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)), w.IsGen ∧
      ∀ t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → PhiRaw D F k y g w s s'
def GtTors (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) : Prop :=
  ∃ h, GtPtF.IsNsmul k g h ∧ h.IsZero
def addφ (D : DegPre R) (a b : D.X) : Fin 10 → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) :=
  let x := fst D.P.A D.P.A; let y := snd D.P.A D.P.A; let c := fun χ => toUnit (D.P.A ⊗ D.P.A) ≫ D.c χ
  ![x.left, (x * c (a + b)).left, (c (a + b)).left, y.left, (y * c (a - b)).left, (c (a - b)).left,
    (x * y * c a).left, (c a).left, (x * y⁻¹ * c b).left, (c b).left]
def addε : Fin 10 → ℤ := ![1, 1, -1, 1, 1, -1, -1, 1, -1, 1]
example (x y a b : ℤ) :
    ∑ k, addε k * (![x, x + (a + b), a + b, y, y + (a - b), a - b, x + y + a, a, x - y + b, b] k) ^ 2 = 0 := by
  simp [Fin.sum_univ_succ, addε]; ring
end
end GlobalTheory.UU
end


