-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:47.633817+00:00
-- url     : https://prove2.me/theorems/8879507d-a24c-4bdd-97a6-f9bf557eb700
-- title:
--   Split Unramified Places
-- statement:
--   Definitions and structural lemmas for Split Unramified Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
section Ring
variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE
def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))
variable {p OE}
@[simp] theorem bar_tmul [StarRing OE] (z : ℤ_[p]) (a : OE) :
    bar p OE (z ⊗ₜ a) = z ⊗ₜ star a := rfl
theorem bar_bar [StarRing OE] (x : Op p OE) : bar p OE (bar p OE x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)
@[simp] theorem extend_tmul {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O)
    (z : ℤ_[p]) (a : OE) : extend σ (z ⊗ₜ a : Op p OE) = algebraMap ℤ_[p] O z * σ a := rfl
end Ring
@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e
namespace Place
variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]
def conj [StarRing OE] (w : Place p OE) : Place p OE where
  e := bar p OE w.e
  idem := w.idem.map (bar p OE)
  ne_zero := fun h => w.ne_zero (by rw [← bar_bar w.e, h, map_zero])
  primitive := fun f hf h => by
    rcases w.primitive (bar p OE f) (hf.map (bar p OE))
      (by rw [← bar_bar w.e, ← map_mul, h]) with h0 | h1
    · left; rw [← bar_bar f, h0, map_zero]
    · right; rw [← h1, bar_bar]
theorem conj_conj [StarRing OE] (w : Place p OE) : w.conj.conj = w :=
  Place.ext (bar_bar w.e)
abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}
def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom
def degree [Module.Finite ℤ OE] (w : Place p OE) : ℕ := Module.finrank ℤ_[p] w.Ow
def Induces (w : Place p OE) {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Prop :=
  extend σ w.e = 1
def Emb (w : Place p OE) (O : Type) [CommRing O] [Algebra ℤ_[p] O] : Type :=
  {σ : OE →+* O // w.Induces σ}
def IsDiffVal_vp [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (w : Place p OE)
    (vd : ℝ) : Prop :=
  ∃ a b : ℕ, 0 < b ∧ vd * b = a ∧
    (differentIdeal ℤ OE).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}
def IsUnramified (w : Place p OE) : Prop := (Ideal.span {(p : w.Ow)}).IsMaximal
end Place
def UnramifiedIn (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] : Prop :=
  ∀ w : Place p OE, w.IsUnramified
structure SplitPlace (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [StarRing OE]
    extends Place p OE where
  ne_conj : toPlace ≠ toPlace.conj
def SplitPlace.conj {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE]
    (w : SplitPlace p OE) : SplitPlace p OE where
  toPlace := w.toPlace.conj
  ne_conj := by rw [Place.conj_conj]; exact w.ne_conj.symm
structure UnrPlace (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] extends Place p OE where
  unramified : toPlace.IsUnramified
section Gauss
variable {p : ℕ} [Fact p.Prime]
def gaussEmb (s : ℤ_[p]) (hs : s * s = -1) : GaussianInt →+* ℤ_[p] :=
  Zsqrtd.lift ⟨s, by simpa using hs⟩
def gaussIdem (s h : ℤ_[p]) : Op p GaussianInt :=
  h ⊗ₜ 1 + (-(h * s)) ⊗ₜ Zsqrtd.sqrtd
theorem gaussEmb_sqrtd (s : ℤ_[p]) (hs : s * s = -1) : gaussEmb s hs Zsqrtd.sqrtd = s := by
  simp [gaussEmb, Zsqrtd.lift]
theorem extend_gaussIdem (s h : ℤ_[p]) (hs : s * s = -1) (hh : 2 * h = 1) :
    extend (gaussEmb s hs) (gaussIdem s h) = 1 := by
  simp only [gaussIdem, map_add, extend_tmul, gaussEmb_sqrtd, map_one, Algebra.algebraMap_self,
    RingHom.id_apply]
  linear_combination hh - h * hs
theorem extend_bar_gaussIdem (s h : ℤ_[p]) (hs : s * s = -1) :
    extend (gaussEmb s hs) (bar p GaussianInt (gaussIdem s h)) = 0 := by
  have : star (Zsqrtd.sqrtd : GaussianInt) = -Zsqrtd.sqrtd := by ext <;> simp
  simp only [gaussIdem, map_add, bar_tmul, this, star_one, extend_tmul, map_neg, gaussEmb_sqrtd,
    map_one, Algebra.algebraMap_self, RingHom.id_apply]
  linear_combination h * hs
theorem mul_gaussIdem (s h : ℤ_[p]) (hs : s * s = -1) (x : Op p GaussianInt) :
    x * gaussIdem s h = algebraMap ℤ_[p] _ (extend (gaussEmb s hs) x) * gaussIdem s h := by
  set I : Op p GaussianInt := 1 ⊗ₜ Zsqrtd.sqrtd with hI
  set A := algebraMap ℤ_[p] (Op p GaussianInt) with hA
  have hII : I * I = -1 := by
    have : (Zsqrtd.sqrtd * Zsqrtd.sqrtd : GaussianInt) = -1 := by ext <;> simp
    rw [hI, Algebra.TensorProduct.tmul_mul_tmul, this, TensorProduct.tmul_neg, one_mul]; rfl
  have hz : ∀ (z : ℤ_[p]) (a : GaussianInt), (z ⊗ₜ a : Op p GaussianInt) = A z * (1 ⊗ₜ a) := by
    intro z a; simp [hA]
  have he : gaussIdem s h = A h - A h * A s * I := by
    rw [gaussIdem, hz h, hz (-(h * s)), map_neg, map_mul]
    show A h * 1 + _ = _
    ring
  have hS : A s * A s = -1 := by rw [← map_mul, hs, map_neg, map_one]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a =>
    have ha : a = (a.re : GaussianInt) + (a.im : GaussianInt) * Zsqrtd.sqrtd := by ext <;> simp
    have h1 : (1 ⊗ₜ a : Op p GaussianInt) = (a.re : Op p GaussianInt) + (a.im : _) * I := by
      have := congrArg (Algebra.TensorProduct.includeRight : GaussianInt →ₐ[ℤ] Op p GaussianInt) ha
      rw [map_add, map_mul, map_intCast, map_intCast] at this
      exact this
    have h2 : gaussEmb s hs a = a.re + a.im * s := by
      conv_lhs => rw [ha]
      rw [map_add, map_mul, map_intCast, map_intCast, gaussEmb_sqrtd]
    rw [extend_tmul, hz, h1, h2, he]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_add, map_intCast]
    linear_combination (A z * (a.im : Op p GaussianInt) * A h) * (- A s * hII + I * hS)
  | add x y hx hy => rw [add_mul, hx, hy, map_add, map_add, add_mul]
def gaussPlace (s h : ℤ_[p]) (hs : s * s = -1) (hh : 2 * h = 1) : SplitPlace p GaussianInt where
  e := gaussIdem s h
  idem := by
    unfold IsIdempotentElem
    rw [mul_gaussIdem s h hs, extend_gaussIdem s h hs hh, map_one, one_mul]
  ne_zero := fun h0 => by
    have := extend_gaussIdem s h hs hh
    rw [h0, map_zero] at this
    exact zero_ne_one this
  primitive := fun f hf hfe => by
    have h1 := mul_gaussIdem s h hs f
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 (hf.map (extend (gaussEmb s hs))) with h0 | h0
    · left; rw [← hfe, h1, h0, map_zero, zero_mul]
    · right; rw [← hfe, h1, h0, map_one, one_mul]
  ne_conj := fun h0 => by
    have h1 : gaussIdem s h = bar p GaussianInt (gaussIdem s h) := congrArg Place.e h0
    have h2 := extend_bar_gaussIdem s h hs
    rw [← h1, extend_gaussIdem s h hs hh] at h2
    exact one_ne_zero h2
def gaussPlaceEmb (s h : ℤ_[p]) (hs : s * s = -1) (hh : 2 * h = 1) :
    (gaussPlace s h hs hh).toPlace.Emb ℤ_[p] :=
  ⟨gaussEmb s hs, extend_gaussIdem s h hs hh⟩
def gaussOwEquiv (s h : ℤ_[p]) (hs : s * s = -1) (hh : 2 * h = 1) :
    (gaussPlace s h hs hh).toPlace.Ow ≃ₐ[ℤ_[p]] ℤ_[p] :=
  (Ideal.quotientEquivAlgOfEq ℤ_[p] (show Ideal.span {1 - gaussIdem s h} =
      RingHom.ker (extend (gaussEmb s hs)) by
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show extend (gaussEmb s hs) (1 - gaussIdem s h) = 0
      rw [map_sub, map_one, extend_gaussIdem s h hs hh, sub_self]
    · intro x hx
      have hx' : extend (gaussEmb s hs) x = 0 := hx
      have h1 := mul_gaussIdem s h hs x
      rw [hx', map_zero, zero_mul] at h1
      exact Ideal.mem_span_singleton'.2 ⟨x, by rw [mul_sub, h1, mul_one, sub_zero]⟩)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := extend (gaussEmb s hs))
      (fun z => ⟨algebraMap _ _ z, by simp⟩))
def gaussUnrPlace (s h : ℤ_[p]) (hs : s * s = -1) (hh : 2 * h = 1) : UnrPlace p GaussianInt where
  toPlace := (gaussPlace s h hs hh).toPlace
  unramified := by
    have hm : (Ideal.span {(p : ℤ_[p])}).IsMaximal := by
      rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
    have : (Ideal.map (gaussOwEquiv s h hs hh).symm.toRingEquiv
        (Ideal.span {(p : ℤ_[p])})).IsMaximal := Ideal.map_isMaximal_of_equiv _
    rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
    exact this
local instance _p2m_local_instance_3272e94269_226 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
end Gauss
example (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (w : Place p (NumberField.RingOfIntegers E)) (vd : ℝ) : Prop :=
  w.IsDiffVal_vp vd ∧ 0 < w.degree
end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces


