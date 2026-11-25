-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:24.642304+00:00
-- url     : https://prove2.me/theorems/10fc42ec-6c4e-42d3-ad59-727e75f5e812
-- title:
--   WCompat
-- statement:
--   Definitions and structural lemmas for WCompat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/WCompat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
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
variable {R : Type} [CommRing R] [IsDomain R]
def IsCPOf (D : DegPre R) (M : CP D.P.A) : Prop :=
  M.L = ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ ∧ HEq M.c D.cub ∧ HEq M.sym D.sym
structure PreU (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where

  semi : IsSemiAbelian G

  gen : (Over.pullback (jK R)).obj G ≅ A.A

  gen_hom : IsMonHom gen.hom

  P : CP G

  wA : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R)))

  wA_gen : wA.IsGen

  gt : ∀ e : ℕ, GtCoord I D e G

  gt_q : ∀ e : ℕ, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left

  gt_t : ∀ (e : ℕ) (χ : D.X), LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ ((gt (e + 1)).t χ) (thickMap R I e G)) ((gt e).t χ)

  w : ∀ e : ℕ, LB.Iso (P.L.L.pull (fstG I e G).left) (D.P.L.pull (gt e).pG.left)

  w_gen : ∀ e, (w e).IsGen

  w_vals : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left)
    (JG : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good P.L.L z JG → Good D.P.L z J →
    ∀ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, W x = gw (w e) x.left z (J (x.left ≫ (gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))) →
      (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (T.hom ≫ thick R I e) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ thick R I e) z JG) ∧
      (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (gt e).pG.left) z J * W x =
        W x⁻¹ * val P.sym (x.left ≫ (fstG I e G).left) z JG) ∧
      ∀ x y u : T ⟶ thickObj R I e G,
        @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
            ((Over.map (thick R I e)).map x ≫ (gt e).pG) ((Over.map (thick R I e)).map y ≫ (gt e).pG)
            ((Over.map (thick R I e)).map u ≫ (gt e).pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map (thick R I e)).obj T) z JG
            ((Over.map (thick R I e)).map x ≫ fstG I e G) ((Over.map (thick R I e)).map y ≫ fstG I e G)
            ((Over.map (thick R I e)).map u ≫ fstG I e G))

  w_compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : D.P.L.ι) (k : P.L.L.ι),
    (gt e).pG.left (x z) ∈ D.P.L.U j → (fstG I e G).left (x z) ∈ P.L.L.U k →
    gw (w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (w e) x z j (fun _ => k)
variable {I : Ideal R} {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def famφT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (α : D.X) : Fin 4 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left, (toUnit (T ⊗ D.P.A) ≫ D.c α).left,
    (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left]
abbrev SecBT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (famφT D T α) (DegPre.famε k))
abbrev PreU.SecGT (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ)))
def PreU.ExpT (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k)
    (f : ∀ α, SecBT D T k α) : Prop :=
  ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left), rG ≫ (snd T G).left = x ≫ (fstG I e G).left →
    rB ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (f α) rB z J = 0) ∧
      (gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => JG (x ≫ (fstG I e G).left))).val ^ k * sval σ rG z JG =
        ∑ α ∈ s, sval (f α) rB z J * (val ((U.gt e).t α) x z J).val
def PreU.Red (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ G) (g : GtPt D T) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (xe : Z ⟶ (thickObj R I e G).left),
    xe ≫ (fstG I e G).left = r ≫ x.left → xe ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
      ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) xe z J = val (g.s χ) r z J
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
abbrev Raw (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
def PreU.ExpF (U : PreU I D A G) (k : ℕ) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecGT (𝟙_ _) k) (f : Fin n → ∀ α, SecBT D (𝟙_ _) k α),
    (∀ i, U.ExpT (𝟙_ _) k (σ i) (f i)) ∧
    (∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
      rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
          ∑ i, gs rA z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (σ i) rG z JG) ∧
    ∀ (α : D.X) (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
        sval (s α) rF z J = ∑ i, gs rF z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (f i α) rB z J
def PhiRaw (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (g : GtPtF D F)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (s s' : Raw D F k) : Prop :=
  ∀ (α : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F y α g.b) (DegPre.deltaε k))), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + y)) (DegPre.famε k) (s' (α + y))
      (DegPre.famφ D F α) (DegPre.famε k) (s α) (DegPre.trPt D F g.b).left (DegPre.phiφ D F y α g.b) (DegPre.deltaε k) u
def CDVR (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] : Prop :=
  IsDiscreteValuationRing V ∧ IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V
example (hG : GlobalFnsSt) (D : DegPre R) : IsCPOf D (CP.ofDegPre hG D) := ⟨rfl, HEq.rfl, HEq.rfl⟩
example (D : DegPre R) (α : D.X) : famφT D (TF (R := R) F) α = DegPre.famφ D F α := rfl
example (D : DegPre R) (k : ℕ) (p : QkPt D F k) (w) (s s' : Fam D F k) :
    PhiRel D F k p w s s' ↔ PhiRaw D F k p.y p.g w s.s s'.s := Iff.rfl
example (p : ℕ) [Fact p.Prime] : CDVR ℤ_[p] := ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.UU
end


