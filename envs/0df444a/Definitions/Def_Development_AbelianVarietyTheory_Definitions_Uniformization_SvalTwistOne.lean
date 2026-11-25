-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:40.875243+00:00
-- url     : https://prove2.me/theorems/b711dea8-d0a8-5987-8f74-176780120772
-- title:
--   Sval Twist One
-- statement:
--   Definitions and structural lemmas for Sval Twist One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/SvalTwistOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
section General
variable {R : Type} [CommRing R]
def Lvl (I : Ideal R) (e : ℕ) {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = p
def AdicSum (I : Ideal R) {Y : Over (Spec (CommRingCat.of R))} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y.left ⟶ X)} {ε : K → ℤ} {Ix : Type} (p : Ix → LB.Sec (LB.LinComb L φ ε)) (S : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ e : ℕ, ∃ s : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J →
    (∀ i ∉ s, sval (p i) r z J = 0) ∧ sval S r z J = ∑ i ∈ s, sval (p i) r z J
end General
variable {R : Type} [CommRing R] [IsDomain R]
def NullFam (I : Ideal R) {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} {k : ℕ} (f : ∀ α, SecBT D T k α) : Prop :=
  ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left), Lvl I e (r ≫ (T ⊗ D.P.A).hom) →
    ∀ (z : Z) (J), Good D.P.L z J → sval (f α) r z J = 0
def IsProdB {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X} (f : SecBT D T k β) (g : SecBT D T l ga)
    (h : SecBT D T m α) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ T ⊗ D.P.A) (z : Z.left) (J), Good D.P.L z J →
    sval h r.left z J = sval f r.left z J * sval g r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd T D.P.A)).val
def ConvT (I : Ideal R) {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} {k l : ℕ} (f : ∀ α, SecBT D T k α)
    (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) : Prop :=
  ∀ α, ∃ p : D.X → SecBT D T (k + l) α, (∀ β, IsProdB (f β) (g (α - β)) (p β)) ∧ AdicSum (Y := T ⊗ D.P.A) I p (h α)
def twist {D : DegPre R} {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) : ∀ α, SecBT D (TA R W) k α :=
  fun α => DVR.SecOps.secScale (scal (R := W) (fst (TA R W) D.P.A).left (a (Multiplicative.ofAdd α)).val) (f α)
def PullT {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {k : ℕ} (f : ∀ α, SecBT D T k α)
    (f' : ∀ α, SecBT D T' k α) : Prop :=
  ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval (f' α) r z J = sval (f α) (r ≫ (ρ ▷ D.P.A).left) z J
def trT (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) : T ⊗ D.P.A ⟶ T ⊗ D.P.A :=
  lift (fst _ _) (padd D.P.A (snd _ _) (fst _ _ ≫ b))
def deltaφT (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (α' α : D.X) (b : T ⟶ D.P.A) :
    Fin 4 ⊕ Fin 4 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  Sum.elim (famφT D T α') (fun i => (trT D b).left ≫ famφT D T α i)
variable {I : Ideal R} {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def PreU.wv (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left) (z : Z)
    (JG : (Z ⟶ G.left) → U.P.L.L.ι) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => JG (x ≫ (fstG I e G).left))
def PreU.TorPt (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (TA R W).left) (xe : Z ⟶ (thickObj R I e G).left),
    xe ≫ (fstG I e G).left = r ≫ x.left → xe ≫ (U.gt e).pG.left = r ≫ (1 : TA R W ⟶ D.P.A).left ∧
      ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
        (val ((U.gt e).t χ) xe z J).val = gs (𝟙 Z) z ⊤ (scal (R := W) r (a (Multiplicative.ofAdd χ)).val)
def PreU.NormAt (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ G)
    (ν : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-1, 1])) : Prop :=
  ν.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (xe oe : Z ⟶ (thickObj R I e G).left),
    xe ≫ (fstG I e G).left = r ≫ x.left → oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → val ν r z JG * U.wv e oe z JG J = U.wv e xe z JG J
def PreU.ProdExp (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) {k l : ℕ} (f : ∀ α, SecBT D T k α)
    (g : ∀ α, SecBT D T l α) (σ : U.SecGT T (k + l)) : Prop :=
  ∀ e : ℕ, ∃ s s' : Finset D.X, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left), rG ≫ (snd T G).left = x ≫ (fstG I e G).left →
    rB ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (f α) rB z J = 0) ∧ (∀ α ∉ s', sval (g α) rB z J = 0) ∧
      (U.wv e x z JG J).val ^ (k + l) * sval σ rG z JG =
        (∑ α ∈ s, sval (f α) rB z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) rB z J * (val ((U.gt e).t α) x z J).val
section Inhabitants
end Inhabitants
end GlobalTheory.UU
end


