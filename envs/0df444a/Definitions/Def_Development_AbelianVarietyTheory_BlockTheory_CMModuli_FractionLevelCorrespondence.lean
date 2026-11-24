-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_FractionLevelCorrespondence
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:37.599421+00:00
-- url     : https://prove2.me/theorems/2f70a692-7c88-42c6-a643-fd7c03871667
-- title:
--   Fraction Level Correspondence
-- statement:
--   Definitions and structural lemmas for Fraction Level Correspondence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FractionLevelCorrespondence.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TateUniformizationInput_IsFracImage_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
section Bundles
variable {X X' T : Scheme.{0}} {K : Type} [Fintype K]
def CorrVia {L' : LB X'} {L : LB X} {φ : X' ⟶ X} (w : LB.Iso L' (L.pull φ))
    (a : K → (T ⟶ X')) (b : K → (T ⟶ X)) (ε : K → ℤ) (t' : LB.Gen (LB.LinComb L' a ε))
    (t : LB.Gen (LB.LinComb L b ε)) (z : Γ(T, ⊤)ˣ) : Prop :=
  (∀ k, b k = a k ≫ φ) ∧
    ∀ (j' : K → L'.ι) (j : K → L.ι) (V : T.Opens) (h' : V ≤ (LB.LinComb L' a ε).U j')
      (h : V ≤ (LB.LinComb L b ε).U j)
      (hw : ∀ k, V ≤ a k ⁻¹ᵁ ((L.pull φ).U (fun _ => j k) ⊓ L'.U (j' k))),
      (∏ k, res (hw k) (pullU (a k) _ (w.s (fun _ => j k, j' k))) ^ ε k) * res h' (t'.s j') =
        res le_top z * res h (t.s j)
end Bundles
section Frac
variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R]
def fracMap (f : O' →+* R) (hf : Function.Injective f) : FractionRing O' →+* FractionRing R :=
  IsFractionRing.lift (g := (algebraMap R (FractionRing R)).comp f)
    ((IsFractionRing.injective R (FractionRing R)).comp hf)
def fracUnit (u : R) (hu : u ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R (FractionRing R) u)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hu)
example : algebraMap (FractionRing R) (FractionRing R) = RingHom.id _ := rfl
end Frac
section Subst
variable {O' : Type} [CommRing O']
def IsSubst (π : O') (ev : PowerSeries O' →+* O') : Prop :=
  (∀ a, ev (PowerSeries.C a) = a) ∧ ev PowerSeries.X = π
lemma exists_isSubst (J : Ideal O') [hJ : IsAdicComplete J O'] {π : O'} (hπ : π ∈ J) :
    ∃ ev, IsSubst π ev := by
  letI : WithIdeal O' := ⟨J⟩
  have hA : IsAdic J := rfl
  obtain ⟨h1, h2⟩ := hA.isAdicComplete_iff.1 hJ
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.eval₂Hom (φ := RingHom.id O') continuous_id ha, fun a => ?_, ?_⟩
  · rw [PowerSeries.coe_eval₂Hom]; simp
  · rw [PowerSeries.coe_eval₂Hom]; simp
lemma IsSubst.unique (J : Ideal O') [IsHausdorff J O'] {π : O'} (hπ : π ∈ J)
    {ev ev' : PowerSeries O' →+* O'} (h : IsSubst π ev) (h' : IsSubst π ev') : ev = ev' := by
  have key : ∀ (n : ℕ) (F : PowerSeries O'), ev F - ev' F ∈ J ^ n := by
    intro n
    induction n with
    | zero => intro F; simp
    | succ n ih =>
      intro F
      have hF := PowerSeries.eq_X_mul_shift_add_const F
      have : ev F - ev' F = π * (ev (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) -
          ev' (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F)) := by
        conv_lhs => rw [hF]
        simp only [map_add, map_mul, h.1, h.2, h'.1, h'.2]
        ring
      rw [this, pow_succ']
      exact Ideal.mul_mem_mul hπ (ih _)
  refine RingHom.ext fun F => sub_eq_zero.1 (IsHausdorff.haus (I := J) inferInstance _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n F
end Subst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
section Twist
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
def IsTwist (x : ArcInput D c β O' b) (f : O' →+* R) (hf : Function.Injective f) (u : R)
    (hu : u ≠ 0) (Δ : OData H I) (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left)
    (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ)) (e : Δ.D.toPre.X ≃ₗ[𝓞 E] x.P.X) : Prop :=
  letI := hostStar H
  IsGrpPullback Δ.D.toPre.P.A x.P.P.A (spMap f) φ ∧
  (∀ a : 𝓞 E, (Δ.ac.onB.act a).left ≫ φ = φ ≫ (x.ac.onB.act a).left) ∧
  w.IsGen ∧
  CorrVia w _ _ _ Δ.D.toPre.rig (LB.pullGen x.P.P.L _ _ x.P.rig (spMap f)) 1 ∧
  (∀ y, (Δ.D.toPre.c y).left ≫ φ = spMap f ≫ (x.P.c (e y)).left) ∧
  ∀ y, CorrVia w _ _ _ (Δ.D.toPre.psi y)
    (LB.pullGen x.P.P.L _ _ (x.P.psi (e y)) (spMap (fracMap f hf)))
    (unitOn (fracUnit u hu ^ (x.be (e y) (e y) / 2)))
def IsTransport (x : ArcInput D c β O' b) (f : O' →+* R) (hf : Function.Injective f) (u : R)
    (hu : u ≠ 0) (Δ : OData H I) (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left)
    (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ)) (e : Δ.D.toPre.X ≃ₗ[𝓞 E] x.P.X) (k : ℕ)
    (p : QkPt x.P (FractionRing O') k) (p' : QkPt Δ.D.toPre (FractionRing R) k) : Prop :=
  e p'.y = p.y ∧
  p'.g.b.left ≫ φ = spMap (fracMap f hf) ≫ p.g.b.left ∧
  ∀ χ : Δ.D.toPre.X, CorrVia w _ _ _ (p'.g.s χ)
    (LB.pullGen x.P.P.L _ _ (p.g.s (e χ)) (spMap (fracMap f hf)))
    (unitOn (fracUnit u hu ^ (x.be p.y (e χ) / (k : ℤ))))
variable {Xo : Moduli D l}
def HasArcUnif (Y : Model Xo c β) (x : ArcInput D c β O' b) (f : O' →+* R) (u : R) (I : Ideal R)
    (χ : Sp R ⟶ Y.X) : Prop :=
  ∃ (hf : Function.Injective f) (hu : u ≠ 0)
    (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (Δ : OData H I) (U : OUnif t Δ)
    (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left) (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ))
    (e : Δ.D.toPre.X ≃ₗ[𝓞 E] x.P.X) (y : Sp (FractionRing R) ⟶ Xo.XF c),
    IsTwist x f hf u hu Δ φ w e ∧
    y ≫ Y.j = spMap (algebraMap R (FractionRing R)) ≫ χ ∧
    (∀ a : D.La, ∃ (p' : QkPt Δ.D.toPre (FractionRing R) l.M)
        (g : TF (R := R) (FractionRing R) ⟶ t.G),
      IsTransport x f hf u hu Δ φ w e l.M (x.lev.eta a) p' ∧
      g.left ≫ m.φ = y ≫ (Y.oF.eta a).left ≫ Y.m.φ ∧ U.ToAk (FractionRing R) l.M p' g) ∧
    ∀ a : D.La, ∃ (p' : QkPt Δ.D.toPre (FractionRing R) l.A)
        (g : TF (R := R) (FractionRing R) ⟶ t.G),
      IsTransport x f hf u hu Δ φ w e l.A (x.lev.etaA a) p' ∧
      g.left ≫ m.φ = y ≫ (Y.oF.etaA a).left ≫ Y.m.φ ∧ U.ToAk (FractionRing R) l.A p' g
end Twist
variable {Xo : Moduli D l}
def IsArc (Y : Model Xo c β) (x : ArcInput D c β O' b) (π : O')
    (χ : Sp (PowerSeries O') ⟶ Y.X) : Prop :=
  χ ≫ Y.s = spMap ((PowerSeries.C : O' →+* PowerSeries O').comp b) ∧
  χ ⁻¹' abLocus Y.t.G =
    {q : PrimeSpectrum (PowerSeries O') | (PowerSeries.X : PowerSeries O') ∉ q.asIdeal} ∧
  (∃ y : Sp (Localization.Away (PowerSeries.C π * PowerSeries.X : PowerSeries O')) ⟶ Xo.XF c,
    y ≫ Y.j = spMap (algebraMap (PowerSeries O') _) ≫ χ) ∧
  HasArcUnif Y x (PowerSeries.C : O' →+* PowerSeries O') PowerSeries.X
    (Ideal.span {PowerSeries.X}) χ
def ArcValue (Y : Model Xo c β) (x : ArcInput D c β O' b) (π : O')
    (χ : Sp (PowerSeries O') ⟶ Y.X) : Prop :=
  ∀ yt : Sp O' ⟶ Y.X, yt ≫ Y.s = spMap b →
    HasArcUnif Y x (RingHom.id O') π (Ideal.span {π}) yt →
    ∀ ev : PowerSeries O' →+* O', IsSubst π ev → spMap ev ≫ χ = yt
def ArcClause (Y : Model Xo c β) : Prop :=
  (∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] (π : O'), Irreducible π →
    ∀ (b : O →+* O') (x : ArcInput D c β O' b),
      ∃ χ : Sp (PowerSeries O') ⟶ Y.X, (∀ χ', IsArc Y x π χ' ↔ χ' = χ) ∧ ArcValue Y x π χ) ∧
  ∀ (O' : Type) [Field O'] (b : O →+* O') (x : ArcInput D c β O' b),
    ∃ χ : Sp (PowerSeries O') ⟶ Y.X, ∀ χ', IsArc Y x 1 χ' ↔ χ' = χ
example (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (π : V) (hπ : Irreducible π) :
    ∃! ev, IsSubst π ev := by
  have h : π ∈ IsLocalRing.maximalIdeal V := hπ.not_isUnit
  obtain ⟨ev, hev⟩ := exists_isSubst _ h
  exact ⟨ev, hev, fun ev' h' => IsSubst.unique _ h h' hev⟩
example (Y : Model Xo c β) (h : ArcClause Y) (F : Type) [Field F] (b : O →+* F)
    (x : ArcInput D c β F b) : ∃! χ, IsArc Y x 1 χ := by
  obtain ⟨χ, hχ⟩ := h.2 F b x
  exact ⟨χ, (hχ χ).2 rfl, fun χ' h' => (hχ χ').1 h'⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FractionLevelCorrespondence


