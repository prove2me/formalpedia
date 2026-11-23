-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:55.85633+00:00
-- url     : https://prove2.me/theorems/2aac61be-3451-43a7-80e3-f4e4611294a3
-- title:
--   Conjugate Place Eigen
-- statement:
--   Definitions and structural lemmas for Conjugate Place Eigen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ConjugatePlaceEigen.lean

import Mathlib
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out
structure HidaSetting (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] : Prop where
  prime : p.Prime
  algClosed : IsAlgClosed C
  charZero : CharZero C
  integers : v.Integers O
  p_lt : v (p : C) < 1
  complete : IsAdicComplete (Ideal.span {(p : O)}) O
section Inhabitant
open Ideal
variable (p : ℕ) [hp : Fact p.Prime]
end Inhabitant
section Places
variable {E : Type} [Field E] [NumberField E]
def IsOver (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Prop := (p : 𝓞 E) ∈ w.asIdeal
abbrev Ow (w : HeightOneSpectrum (𝓞 E)) : Type := w.adicCompletionIntegers E
def ramIdx (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  multiplicity w.asIdeal (Ideal.span {(p : 𝓞 E)})
def localDeg (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  ramIdx p w * w.asIdeal.inertiaDeg ℤ
def diffVal_vp (p : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℝ :=
  (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) : ℝ) / (ramIdx p w : ℝ)
abbrev PadicOrder (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : Type := ℤ_[p] ⊗[ℤ] 𝓞 E
def toPadic (p : ℕ) [Fact p.Prime] (E : Type) [Field E] : 𝓞 E →+* PadicOrder p E :=
  (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] PadicOrder p E).toRingHom
def IsPlaceIdem (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) (e : PadicOrder p E) : Prop :=
  IsIdempotentElem e ∧ e - 1 ∈ w.asIdeal.map (toPadic p E) ∧
    ∀ w' : HeightOneSpectrum (𝓞 E), IsOver p w' → w' ≠ w → e ∈ w'.asIdeal.map (toPadic p E)
def ApproxIdem (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : 𝓞 E) : Prop :=
  ∃ e : PadicOrder p E, IsPlaceIdem p w e ∧
    toPadic p E a - e ∈ Ideal.span {((p : PadicOrder p E)) ^ n}
def EmbOver {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
    (w : HeightOneSpectrum (𝓞 E)) (τ : 𝓞 E →+* O) : Prop :=
  ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ v (algebraMap O C (τ a)) < 1
def typeOf (K : Type) [Field K] [Algebra K E] {O : Type} [CommRing O] (κ : 𝓞 K →+* O) :
    Set (𝓞 E →+* O) :=
  {τ | τ.comp (algebraMap (𝓞 K) (𝓞 E)) = κ}
variable [IsCMField E]
def conjInt (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  (IsCMField.ringOfIntegersComplexConj E).toRingEquiv
def conjEmb {O : Type} [CommRing O] (τ : 𝓞 E →+* O) : 𝓞 E →+* O :=
  τ.comp (conjInt E).toRingHom
def conjPlace (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := w.asIdeal.comap (conjInt E).toRingHom
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h => w.ne_bot (by
    rw [eq_bot_iff] at h ⊢
    intro a ha
    have : (conjInt E).symm a ∈ w.asIdeal.comap (conjInt E).toRingHom := by
      rw [Ideal.mem_comap]
      show conjInt E ((conjInt E).symm a) ∈ w.asIdeal
      rwa [RingEquiv.apply_symm_apply]
    simpa using h this)
def SplitOn (K : Type) [Field K] [Algebra K E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E)) ≠
    (conjPlace w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 E))
end Places
section Eigen
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {R : Type} [CommRing R] (α : RingAct G R)
def dAct (a : R) (x : LieG G) : LieG G :=
  ⟨x.1 ≫ α.act a, by
    haveI := α.hom a
    rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩
def LieEig (τ : R →+* O) : Type :=
  {x : LieG G // ∀ a : R, x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1}
def omegaEig (τ : R →+* O) : Submodule O (LieEig α τ → O) where
  carrier := {f | (∀ x y z : LieEig α τ, z.1.1 = x.1.1 * y.1.1 → f z = f x + f y) ∧
    ∀ (c : O) (x z : LieEig α τ), z.1.1 = ptMap (dualScale c) ≫ x.1.1 → f z = c * f x}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun x y z h => by
        simp only [Pi.add_apply]; rw [hf1 x y z h, hg1 x y z h]; ring,
      fun c x z h => by
        simp only [Pi.add_apply]; rw [hf2 c x z h, hg2 c x z h]; ring⟩
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun x y z h => by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [hf1 x y z h]; ring,
      fun a x z h => by
        simp only [Pi.smul_apply, smul_eq_mul]; rw [hf2 a x z h]; ring⟩
def restrictEig (τ : R →+* O) : (LieG G → O) →ₗ[O] (LieEig α τ → O) :=
  LinearMap.funLeft O O Subtype.val
def HasEigRank (τ : R →+* O) (r : ℕ) : Prop :=
  ∃ b : (Fin r → O) ≃ LieEig α τ,
    (∀ s t, (b (s + t)).1.1 = (b s).1.1 * (b t).1.1) ∧
    ∀ (c : O) s, (b (c • s)).1.1 = ptMap (dualScale c) ≫ (b s).1.1
def eigRank (τ : R →+* O) : ℕ := Module.finrank O (omegaEig α τ)
def htEig (p : ℕ) (τ : R →+* O) : Submodule O (omegaEig α τ) :=
  ((htSpan G p).map (restrictEig α τ)).comap (omegaEig α τ).subtype
def HasColength_vp (p : ℕ) {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    (τ : R →+* O) (a : ℝ) : Prop :=
  0 ≤ a ∧ ReciprocityTheory.PGsh.Up.HasLen v O (omegaEig α τ ⧸ htEig α p τ) (v (p : C) ^ a)
example (τ : R →+* O) (f : LieG G → O) (hf : f ∈ omega G) :
    restrictEig α τ f ∈ omegaEig α τ := by
  refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
  · have := hf.1 x.1 y.1 (h ▸ z.1.2)
    show f z.1 = f x.1 + f y.1
    rw [← this]; congr 1; exact Subtype.ext h
  · have := hf.2 c x.1 (h ▸ z.1.2)
    show f z.1 = c * f x.1
    rw [← this]; congr 1; exact Subtype.ext h
end Eigen
section Arith
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {E : Type} [Field E] [NumberField E] (α : RingAct G (𝓞 E))
def IsPlaceChar (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) (χ : Tv G p) : Prop :=
  ∀ (n : ℕ) (a : 𝓞 E), ApproxIdem p w n a →
    ∀ (T : Over (Spec (CommRingCat.of O))) (x y : T ⟶ torsion G (p ^ n)),
      x ≫ torsion.ι G (p ^ n) ≫ α.act a = y ≫ torsion.ι G (p ^ n) → x ≫ χ.χ n = y ≫ χ.χ n
def htSpanAt (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) : Submodule O (LieG G → O) :=
  Submodule.span O {f | f ∈ omega G ∧ ∃ χ : Tv G p, IsPlaceChar α p w χ ∧ IsAl χ f}
def htEigAt (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) (τ : 𝓞 E →+* O) :
    Submodule O (omegaEig α τ) :=
  ((htSpanAt α p w).map (restrictEig α τ)).comap (omegaEig α τ).subtype
def IsCharAction {𝓔 : SplitExt (Spec (CommRingCat.of O))} (D : 𝓔.GtDatum G)
    (m : Module (𝓞 E) 𝓔.X) : Prop :=
  letI := m
  ∀ a : 𝓞 E, ∃ t : splitTorus (Spec (CommRingCat.of O)) 𝓔.X ⟶ splitTorus _ 𝓔.X,
    t ≫ D.i = D.i ≫ α.act a ∧
      ∀ χ : 𝓔.X, t.left.appTop.hom (charUnit _ 𝓔.X χ).val = (charUnit _ 𝓔.X (a • χ)).val
def HasToricRank {𝓔 : SplitExt (Spec (CommRingCat.of O))} (D : 𝓔.GtDatum G) (ρ : ℕ) : Prop :=
  ∃ m : Module (𝓞 E) 𝓔.X, IsCharAction α D m ∧
    (letI := m; Module.finrank E (E ⊗[𝓞 E] 𝓔.X) = ρ)
variable [IsCMField E]
def HasSignatureOn (Ψ : Set (𝓞 E →+* O)) (rp rm : ℕ) : Prop :=
  ∀ τ ∈ Ψ, HasEigRank α τ rp ∧ HasEigRank α (conjEmb τ) rm
def HasSignatureAt {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    (w : HeightOneSpectrum (𝓞 E)) (rp rm : ℕ) : Prop :=
  HasSignatureOn α {τ | EmbOver v w τ} rp rm
def IsJPrime {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]
    (w : HeightOneSpectrum (𝓞 E)) (r j' : ℕ) : Prop :=
  j' ≤ r ∧ HasSignatureAt α v w (r - j') j'
end Arith
def PlaceIdemSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)),
    IsOver p w → (∃! e, IsPlaceIdem p w e) ∧
      ∀ e, IsPlaceIdem p w e → ∃ φ : (PadicOrder p E ⧸ Ideal.span {1 - e}) ≃+* Ow w,
        ∀ a : 𝓞 E, φ (Ideal.Quotient.mk _ (toPadic p E a)) = algebraMap (𝓞 E) (Ow w) a
def EmbOverSt : Prop :=
  ∀ (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    HidaSetting p v O → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
      (w : HeightOneSpectrum (𝓞 E)), IsOver p w →
      {τ : 𝓞 E →+* O | EmbOver v w τ}.Finite ∧
      {τ : 𝓞 E →+* O | EmbOver v w τ}.ncard = localDeg p w ∧ 0 < localDeg p w ∧
      (∀ τ : 𝓞 E →+* O, EmbOver v w τ ↔ EmbOver v (conjPlace w) (conjEmb τ)) ∧
      ∀ (K : Type) [Field K] [NumberField K] [Algebra K E], IsTotallyComplex K →
        Module.finrank ℚ K = 2 → SplitOn K w →
        ∃ κ : 𝓞 K →+* O, ∀ τ : 𝓞 E →+* O, EmbOver v w τ →
          τ ∈ typeOf K κ ∧ conjEmb τ ∉ typeOf K κ
def RankSt : Prop :=
  ∀ (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    HidaSetting p v O → ∀ (E : Type) [Field E] [NumberField E]
      (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
      ∀ (α : RingAct G (𝓞 E)) (τ : 𝓞 E →+* O),
        (∀ r, HasEigRank α τ r ↔ r = eigRank α τ) ∧
        Nonempty (omegaEig α τ ≃ₗ[O] (Fin (eigRank α τ) → O)) ∧
        (omega G).map (restrictEig α τ) = omegaEig α τ ∧
        ∀ f ∈ omega G, restrictEig α τ f = 0 ↔ ∃ c : O, c ≠ 0 ∧ c • f ∈ Submodule.span O
          {h | ∃ g ∈ omega G, ∃ a : 𝓞 E, h = g ∘ dAct α a - τ a • g}
def PlacePartSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C], HidaSetting p v O → ∀ (E : Type) [Field E] [NumberField E]
      (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
      ∀ (α : RingAct G (𝓞 E)) (w : HeightOneSpectrum (𝓞 E)), IsOver p w →
        ∀ τ : 𝓞 E →+* O, EmbOver v w τ → htEigAt α p w τ = htEig α p τ ∧
          ∀ a a' : ℝ, HasColength_vp α p v τ a → HasColength_vp α p v τ a' → a = a'
def ToricRankSt : Prop :=
  ∀ (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    HidaSetting p v O → ∀ (E : Type) [Field E] [NumberField E]
      (𝓔 : SplitExt (Spec (CommRingCat.of O))) [IsCommMonObj 𝓔.B]
      [IsCommMonObj (splitTorus (Spec (CommRingCat.of O)) 𝓔.X)]
      (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (D : 𝓔.GtDatum G)
      (α : RingAct G (𝓞 E)) (β : RingAct 𝓔.B (𝓞 E))
      (αT : RingAct (splitTorus (Spec (CommRingCat.of O)) 𝓔.X) (𝓞 E)),
      (∀ a, α.act a ≫ D.q = D.q ≫ β.act a) → (∀ a, αT.act a ≫ D.i = D.i ≫ α.act a) →
      (∃! ρ, HasToricRank α D ρ) ∧ ∀ ρ, HasToricRank α D ρ → ∀ σ : 𝓞 E →+* O,
        HasEigRank αT σ ρ ∧ ∃ r, HasEigRank β σ r ∧ HasEigRank α σ (r + ρ)
end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen


