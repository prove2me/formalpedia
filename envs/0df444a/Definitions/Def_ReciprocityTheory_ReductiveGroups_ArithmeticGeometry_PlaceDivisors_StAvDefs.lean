-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:35.752361+00:00
-- url     : https://prove2.me/theorems/c2ce4ee2-39ec-4dd5-adce-6406f4664f44
-- title:
--   St Av Defs
-- statement:
--   Definitions and structural lemmas for St Av Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/StAvDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
section Lie
variable {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
  {OE : Type} [CommRing OE] (io : Out.RingAct G OE)
def lieAct (a : OE) (x : LieG G) : LieG G :=
  ⟨x.1 ≫ io.act a, by
    rw [← Category.assoc, x.2, Category.assoc]
    haveI := io.hom a
    rw [IsMonHom.one_hom]⟩
theorem fst_scale (c : O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ ptMap (dualScale c) = ptMap (TrivSqZeroExt.fstHom O O O) := by

  have h : ((TrivSqZeroExt.fstHom O O O).toRingHom).comp (dualScale c).toRingHom =
      (TrivSqZeroExt.fstHom O O O).toRingHom := by
    refine RingHom.ext fun x => ?_
    simp [dualScale]
  apply Over.OverMorphism.ext
  simp only [ptMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
def lieScale (c : O) (x : LieG G) : LieG G :=
  ⟨ptMap (dualScale c) ≫ x.1, by rw [← Category.assoc, fst_scale]; exact x.2⟩
def IsEig (τ : OE →+* O) (x : LieG G) : Prop := ∀ a : OE, lieAct G io a x = lieScale G (τ a) x
def LieTau (τ : OE →+* O) : Type := {x : LieG G // IsEig G io τ x}
def restr (τ : OE →+* O) : (LieG G → O) →ₗ[O] (LieTau G io τ → O) :=
  LinearMap.funLeft O O (fun x : LieTau G io τ => x.1)
def omTau (τ : OE →+* O) : Submodule O (LieTau G io τ → O) := (omega G).map (restr G io τ)
def rTau (τ : OE →+* O) : ℕ := Module.finrank O (omTau G io τ)
variable (p : ℕ)
def htTau (τ : OE →+* O) : Submodule O (LieTau G io τ → O) := (htSpan G p).map (restr G io τ)
def HasATau {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C] (τ : OE →+* O) (x : NNReal) :
    Prop :=
  ReciprocityTheory.PGsh.Up.HasLen v O (omTau G io τ ⧸ (htTau G io p τ).comap (omTau G io τ).subtype) x
end Lie
section Place
variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [StarRing OE]
def sig : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE) :=
  Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p])
    (((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom.toIntAlgHom)
structure Place where
  e : ℤ_[p] ⊗[ℤ] OE
  idem : e * e = e
  ne_zero : e ≠ 0
  prim : ∀ f : ℤ_[p] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e
  split : sig p OE e ≠ e
variable {p OE}
def Place.bar (w : Place p OE) : ℤ_[p] ⊗[ℤ] OE := sig p OE w.e
def Place.Ow (w : Place p OE) : Submodule ℤ_[p] (ℤ_[p] ⊗[ℤ] OE) :=
  LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)
def Place.n (w : Place p OE) : ℕ := Module.finrank ℤ_[p] w.Ow
variable {O : Type} [CommRing O] [Algebra ℤ_[p] O]
def tauExt (τ : OE →+* O) : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) τ.toIntAlgHom (fun _ _ => Commute.all _ _)
def Emb (e : ℤ_[p] ⊗[ℤ] OE) : Set (OE →+* O) := {τ | tauExt τ e = 1}
end Place
section Signature
variable (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
  {OE : Type} [CommRing OE] [StarRing OE] (io : Out.RingAct G OE)
def Sig (w : Place p OE) (rp rm : ℕ) : Prop :=
  (∀ τ ∈ Emb (O := O) w.e, rTau G io τ = rp) ∧ (∀ τ ∈ Emb (O := O) w.bar, rTau G io τ = rm)
def jPrime (rm : ℕ) : ℕ := rm
def rhoOf (X : Type) [AddCommGroup X] : ℕ := Module.finrank ℤ X / Module.finrank ℤ OE
def HasVd {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C] (w : Place p OE)
    (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ) : Prop :=
  ∃ b : Module.Basis (Fin w.n) ℤ_[p] w.Ow,
    (v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) : ℝ) =
      (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd)
end Signature
section Statement
def AvAtSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
      (E : SplitExt (Spec (CommRingCat.of O))) (B : Out.PolAV (Spec (CommRingCat.of O)))
      (hBA : B.A = E.B) (_ : HEq B.grp E.grpB) (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
      [IsCommMonObj G] (D : E.GtDatum G), 0 < B.g →
      ∀ (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
        [Module.Finite ℤ OE] [StarRing OE] (io : Out.RingAct G OE) (o : B.OAct OE),
      (∀ a : OE, io.act a ≫ D.q = D.q ≫ eqToHom hBA.symm ≫ o.act a ≫ eqToHom hBA) →
      ∀ (w : Place p OE) (rp rm : ℕ), Sig p G io w rp rm →
      ∀ (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd →
      ∃ x : Fin w.n → NNReal, (∀ j, HasATau G io p v ((t j : Emb (O := O) w.e) : OE →+* O) (x j)) ∧
        v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, x j
structure PlaceU (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where
  e : ℤ_[p] ⊗[ℤ] OE
  idem : e * e = e
  ne_zero : e ≠ 0
  prim : ∀ f : ℤ_[p] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e
def PlaceU.n {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] (w : PlaceU p OE) : ℕ :=
  Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))
def UpAtSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O]
      (E : SplitExt (Spec (CommRingCat.of O))) (B : Out.PolAV (Spec (CommRingCat.of O)))
      (hBA : B.A = E.B) (_ : HEq B.grp E.grpB) (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
      [IsCommMonObj G] (D : E.GtDatum G), 0 < B.g → p ≠ 2 →
      ∀ (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
        [Module.Finite ℤ OE] [StarRing OE] (io : Out.RingAct G OE) (o : B.OAct OE),
      ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
      (∀ a : OE, io.act a ≫ D.q = D.q ≫ eqToHom hBA.symm ≫ o.act a ≫ eqToHom hBA) →
      ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
      (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
      (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
          (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ IsLocalRing.maximalIdeal O) →
      ∀ j : Fin w.n, ∃ x : NNReal, HasATau G io p v ((t j : Emb (O := O) w.e) : OE →+* O) x ∧
        v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
          (rTau G io (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ x
end Statement
end ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs


