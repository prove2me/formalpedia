-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:36.38621+00:00
-- url     : https://prove2.me/theorems/9c0d3d4f-4896-4a69-8271-1da0a787416b
-- title:
--   TXFrame
-- statement:
--   Definitions and structural lemmas for TXFrame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/TXFrame.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UT
def SumI {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E) (s : E) : Prop :=
  ∃ N : Submodule R E, N.FG ∧ s ∈ N ∧ (∀ i, x i ∈ N) ∧
    ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → s - ∑ i ∈ T, x i ∈ I ^ n • N
variable {R : Type} [CommRing R] [IsDomain R]
def SumF (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] {Ix : Type} (x : Ix → F) (s : F) : Prop :=
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R)); SumI I x s
section
variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
def cst (z : (TF (R := R) F).left) (x : F) : (TF (R := R) F).left.presheaf.stalk z :=
  gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x)
abbrev Frm (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : Type := LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b) (DegPre.lineε k))
def rigV {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r z J
variable {D F}
def IsCoef (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (χ : D.X)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))) (x : F) : Prop :=
  ∀ (z : (TF (R := R) F).left) (J), Good D.P.L z J →
    cst F z x * (rigV D (TF (R := R) F).hom z J).val ^ k =
      sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J * (val (g.s χ) (𝟙 _) z J).val * (val w (𝟙 _) z J).val
def coef {k : ℕ} (s : Fam D F k) (g : GtPtF D F) (w : Frm D F k g.b) (χ : D.X) : F :=
  Classical.epsilon (IsCoef k g w χ (s.s χ))
def FrmOne {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) : Prop :=
  w.IsGen ∧ ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = 1
def Normd {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (LB.oneGen D.P.L)
abbrev kapLB (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k' k : ℕ) : LB D.P.A.left :=
  LB.LinComb D.P.L (K := Fin 3) ![𝟙 _, a.left, (1 : D.P.A ⟶ D.P.A).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k']
def TXFrame (N : ℕ) (p : QkPt D F N) (w : Frm D F N p.g.b) : Prop :=
  w.IsGen ∧
  (∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]),
    Normd ν → ∀ z J, Good D.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J) ∧
  ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
    val w (𝟙 _) z J ^ N * val κ p.g.b.left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J
def IsTor (t : Multiplicative D.X →* Fˣ) (g : GtPtF D F) : Prop :=
  g.b = 1 ∧ ∀ χ z J, Good D.P.L z J → (val (g.s χ) (𝟙 _) z J).val = cst F z (t (Multiplicative.ofAdd χ)).val
end
variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
abbrev SecA (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))
def sA {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (t : SecA A F k) {Z : Scheme.{0}}
    (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J : (Z ⟶ A.A.left) → A.L.ι) : Z.presheaf.stalk z :=
  sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t r z J
abbrev W0 (U : UnifPre I D A G) : Type := LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))
def NormW (U : UnifPre I D A G) (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) : Prop :=
  w₀.IsGen ∧ ρ.IsGen ∧ ∀ (z : Spec (CommRingCat.of (FractionRing R))) (JA) (JG), Good A.L z JA → Good U.LG.L z JG →
    gw w₀ (eSec ((Over.pullback (jK R)).obj G)) z (JG (jK R ≫ eSec G)) (fun _ => JA (eSec A.A)) *
        val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _) z JA =
      val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z JG
structure EndU (U : UnifPre I D A G) where
  aG : G ⟶ G
  aA : A.A ⟶ A.A
  aB : D.toPre.P.A ⟶ D.toPre.P.A
  homG : IsMonHom aG
  homA : IsMonHom aA
  homB : IsMonHom aB
  h : D.toPre.X →+ D.toPre.X
  ext : (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA
  q_lin : ∀ e, (Over.pullback (thick R I e)).map aG ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map aB
  i_lin : ∀ e, ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X,
    TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map aG = t ≫ (U.gt e).i
  u : ∀ χ, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.Oφ (𝟙 _) (h χ)) (D.toPre.Oφ aB χ)) (Sum.elim Oε Oinvε))
  u_norm : ∀ χ, Normd (u χ)
  t_lin : ∀ e χ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
    val ((U.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map aG).left) z J =
      val ((U.gt e).t (h χ)) x z J * val (u χ) (x ≫ (U.gt e).pG.left) z J
def EndU.Act {U : UnifPre I D A G} (E : EndU U) {F : Type} [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F) : Prop :=
  g'.b = g.b ≫ E.aB ∧ ∀ χ z J, Good D.toPre.P.L z J →
    val (g'.s χ) (𝟙 _) z J = val (g.s (E.h χ)) (𝟙 _) z J * val (E.u χ) g.b.left z J
def Cross {F : Type} [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A) {j j' : ℕ} (t₁ t₂ : SecA A F j) (t₁' t₂' : SecA A F j') : Prop :=
  ∀ z J, Good A.L z J → sA t₁ (TFK (R := R) F ◁ a).left z J * sA t₂' (𝟙 _) z J = sA t₂ (TFK (R := R) F ◁ a).left z J * sA t₁' (𝟙 _) z J
def IndAt (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (p : QkPt D.toPre F N)
    (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) : Prop :=
  ψ ≫ fst _ _ = fst _ _ ∧ ∀ w₀ : W0 U, w₀.IsGen →
    ∃ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (ψ ≫ snd _ _).left] ![(N : ℤ), -(N : ℤ)]))
      (w : Frm D.toPre F N p.g.b), α.IsGen ∧ w.IsGen ∧ ∀ (t t' : SecA A F N) s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' →
        IsTwistPull A.A A.L ψ (ψ ≫ snd _ _) rfl N N α t t' → PhiRel D.toPre F N p w s s'
def AllU (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G],
    Unif I D A G → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif I D A G, p U
def AllUF (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G],
    Unif I D A G → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  AllU fun {R} _ _ {_} {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], p U F
def AllD (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}, DegData R I →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], p D F
def Tors (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A)) : Prop :=
  (∀ p x, QkToAkU U F k p x ↔ x = f p) ∧ (∀ x, x ^ k = 1 → ∃ p, f p = x) ∧ (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧
  (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
  ∀ p p' (z : Fˣ), WeilQkIs D.toPre F k p p' z ↔ WeilIs A.A A.L k (f p) (f p') (unitOn z)
def LL : Prop := Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5
end GlobalTheory.UT
end


