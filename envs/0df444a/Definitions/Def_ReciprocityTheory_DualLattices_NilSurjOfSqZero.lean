-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- name    : ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:00.559205+00:00
-- url     : https://prove2.me/theorems/8a4199d4-f01f-4abc-b67b-3757d14520dc
-- title:
--   Nil Surj Of Sq Zero
-- statement:
--   Definitions and structural lemmas for Nil Surj Of Sq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NilSurjOfSqZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
def unitSub {A : Type u} [CommRing A] (e : A) (he : e * e = 0) : Aˣ :=
  ⟨1 - e, 1 + e, by linear_combination -he, by linear_combination -he⟩
@[simp] lemma unitSub_val {A : Type u} [CommRing A] (e : A) (he : e * e = 0) :
    (unitSub e he : A) = 1 - e := rfl
section FP
variable {R₁ R₂ R : LAlg R₀} (f₁ : LHom R₁ R) (f₂ : LHom R₂ R)
def fpSub : Subalgebra R₀ (R₁.carrier × R₂.carrier) :=
  AlgHom.equalizer (f₁.1.comp (AlgHom.fst R₀ R₁ R₂)) (f₂.1.comp (AlgHom.snd R₀ R₁ R₂))
lemma mem_fpSub (x : R₁.carrier × R₂.carrier) : x ∈ fpSub f₁ f₂ ↔ f₁.1 x.1 = f₂.1 x.2 := Iff.rfl
lemma fp_isUnit (x : fpSub f₁ f₂) (h : IsUnit x.1.1) : IsUnit x := by
  have hx := (mem_fpSub f₁ f₂ x.1).1 x.2
  have h2 : IsUnit x.1.2 := f₂.2.map_nonunit _ (by
    have h1 : IsUnit (f₂.1 x.1.2) := hx ▸ h.map f₁.1
    exact h1)
  have hu : (h.unit : R₁.carrier) = x.1.1 := IsUnit.unit_spec h
  have hv : (h2.unit : R₂.carrier) = x.1.2 := IsUnit.unit_spec h2
  have hmem : ((↑h.unit⁻¹ : R₁.carrier), (↑h2.unit⁻¹ : R₂.carrier)) ∈ fpSub f₁ f₂ := by
    rw [mem_fpSub]
    show f₁.1 ↑h.unit⁻¹ = f₂.1 ↑h2.unit⁻¹
    calc f₁.1 ↑h.unit⁻¹ = f₁.1 ↑h.unit⁻¹ * (f₂.1 ↑h2.unit * f₂.1 ↑h2.unit⁻¹) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = (f₁.1 ↑h.unit⁻¹ * f₁.1 ↑h.unit) * f₂.1 ↑h2.unit⁻¹ := by
          rw [hu, hv, ← hx]
          ring
      _ = f₂.1 ↑h2.unit⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · show x.1.1 * ↑h.unit⁻¹ = 1
    exact h.mul_val_inv
  · show x.1.2 * ↑h2.unit⁻¹ = 1
    exact h2.mul_val_inv
instance fp_local : IsLocalRing (fpSub f₁ f₂) := by
  have : Nontrivial (fpSub f₁ f₂) := ⟨⟨0, 1, fun h =>
    zero_ne_one (α := (R₁ : Type u)) (congrArg (fun z : fpSub f₁ f₂ => z.1.1) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.1.1 with h | h
  · exact Or.inl (fp_isUnit f₁ f₂ x h)
  · exact Or.inr (fp_isUnit f₁ f₂ (1 - x) h)
def FP : LAlg R₀ := { carrier := fpSub f₁ f₂ }
def FP.p₁ : LHom (FP f₁ f₂) R₁ :=
  ⟨(AlgHom.fst R₀ R₁ R₂).comp (fpSub f₁ f₂).val, ⟨fun x h => fp_isUnit f₁ f₂ x h⟩⟩
lemma FP.mem (x : (FP f₁ f₂ : Type u)) : f₁.1 x.1.1 = f₂.1 x.1.2 := (mem_fpSub f₁ f₂ x.1).1 x.2
def FP.p₂ : LHom (FP f₁ f₂) R₂ :=
  ⟨(AlgHom.snd R₀ R₁ R₂).comp (fpSub f₁ f₂).val, ⟨fun x h => fp_isUnit f₁ f₂ x
    (f₁.2.map_nonunit _ (by convert h.map f₂.1 using 1; exact FP.mem f₁ f₂ x))⟩⟩
@[simp] lemma FP.p₁_apply (x : (FP f₁ f₂ : Type u)) : (FP.p₁ f₁ f₂).1 x = x.1.1 := rfl
@[simp] lemma FP.p₂_apply (x : (FP f₁ f₂ : Type u)) : (FP.p₂ f₁ f₂).1 x = x.1.2 := rfl
def FP.lift {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) : LHom T (FP f₁ f₂) :=
  ⟨(g₁.1.prod g₂.1).codRestrict (fpSub f₁ f₂) (fun t => (mem_fpSub f₁ f₂ _).2 (h t)),
    ⟨fun t ht => g₁.2.map_nonunit t (ht.map (FP.p₁ f₁ f₂).1)⟩⟩
@[simp] lemma FP.lift_fst {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) (t : (T : Type u)) :
    ((FP.lift f₁ f₂ g₁ g₂ h).1 t).1.1 = g₁.1 t := rfl
@[simp] lemma FP.lift_snd {T : LAlg R₀} (g₁ : LHom T R₁) (g₂ : LHom T R₂)
    (h : ∀ t, f₁.1 (g₁.1 t) = f₂.1 (g₂.1 t)) (t : (T : Type u)) :
    ((FP.lift f₁ f₂ g₁ g₂ h).1 t).1.2 = g₂.1 t := rfl
end FP
namespace DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
lemma π_η : Dp.π.1 Dp.η = 0 := by
  have h : Dp.η ∈ RingHom.ker Dp.π.1 := by
    rw [Dp.ker_eq]
    exact Ideal.mem_span_singleton_self _
  exact RingHom.mem_ker.mp h
lemma mem_span_of_π (b : (Dp.D : Type u)) (h : Dp.π.1 b = 0) : b ∈ Ideal.span {Dp.η} := by
  rw [← Dp.ker_eq]
  exact RingHom.mem_ker.mpr h
lemma mul_η (d : (Dp.D : Type u)) : d * Dp.η = Dp.σ.1 (Dp.π.1 d) * Dp.η := by
  have h : d - Dp.σ.1 (Dp.π.1 d) ∈ Ideal.span {Dp.η} :=
    Dp.mem_span_of_π _ (by rw [map_sub, Dp.sect, sub_self])
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have h2 : (d - Dp.σ.1 (Dp.π.1 d)) * Dp.η = 0 := by rw [← hc, mul_assoc, Dp.η_sq, mul_zero]
  linear_combination h2
lemma exists_decomp (b : (Dp.D : Type u)) :
    ∃ s : (R : Type u), b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 s * Dp.η := by
  have h : b - Dp.σ.1 (Dp.π.1 b) ∈ Ideal.span {Dp.η} :=
    Dp.mem_span_of_π _ (by rw [map_sub, Dp.sect, sub_self])
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨Dp.π.1 c, ?_⟩
  rw [← Dp.mul_η c, hc]
  ring
def κ (b : (Dp.D : Type u)) : (R : Type u) := Classical.choose (Dp.exists_decomp b)
lemma decomp (b : (Dp.D : Type u)) : b = Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b) * Dp.η :=
  Classical.choose_spec (Dp.exists_decomp b)
lemma decomp_unique {b : (Dp.D : Type u)} {r s : (R : Type u)}
    (h : b = Dp.σ.1 r + Dp.σ.1 s * Dp.η) : r = Dp.π.1 b ∧ s = Dp.κ b := by
  have hr : r = Dp.π.1 b := by rw [h, map_add, map_mul, Dp.sect, Dp.π_η, mul_zero, add_zero]
  refine ⟨hr, ?_⟩
  have h2 := Dp.decomp b
  have h3 : Dp.σ.1 (s - Dp.κ b) * Dp.η = 0 := by
    rw [map_sub, sub_mul]
    linear_combination h2 - h - congrArg Dp.σ.1 hr
  exact (sub_eq_zero.mp (Dp.free _ h3))
lemma κ_σ (r : (R : Type u)) : Dp.κ (Dp.σ.1 r) = 0 :=
  (Dp.decomp_unique (b := Dp.σ.1 r) (r := r) (s := 0) (by simp)).2.symm
lemma κ_add (b b' : (Dp.D : Type u)) : Dp.κ (b + b') = Dp.κ b + Dp.κ b' := by
  have h := Dp.decomp b
  have h' := Dp.decomp b'
  refine (Dp.decomp_unique (b := b + b') (r := Dp.π.1 b + Dp.π.1 b') (s := Dp.κ b + Dp.κ b') ?_).2.symm
  rw [map_add, map_add]
  linear_combination h + h'
lemma κ_mul (b b' : (Dp.D : Type u)) :
    Dp.κ (b * b') = Dp.π.1 b * Dp.κ b' + Dp.π.1 b' * Dp.κ b := by
  have h := Dp.decomp b
  have h' := Dp.decomp b'
  refine (Dp.decomp_unique (b := b * b') (r := Dp.π.1 b * Dp.π.1 b')
    (s := Dp.π.1 b * Dp.κ b' + Dp.π.1 b' * Dp.κ b) ?_).2.symm
  rw [map_mul, map_add, map_mul, map_mul]
  linear_combination b' * h + (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b) * Dp.η) * h' +
    (Dp.σ.1 (Dp.κ b) * Dp.σ.1 (Dp.κ b')) * Dp.η_sq
lemma κ_algebraMap (c : R₀) : Dp.κ (algebraMap R₀ (Dp.D : Type u) c) = 0 := by
  rw [← Dp.σ.1.commutes c, Dp.κ_σ]
lemma κ_one : Dp.κ 1 = 0 := by
  rw [← map_one Dp.σ.1, Dp.κ_σ]
lemma κ_zero : Dp.κ 0 = 0 := by
  rw [← map_zero Dp.σ.1, Dp.κ_σ]
def frAlg (r : (R : Type u)) : (Dp.D : Type u) →ₐ[R₀] (Dp.D : Type u) where
  toFun b := Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η
  map_one' := by rw [map_one, map_one, Dp.κ_one, zero_mul, map_zero, zero_mul, add_zero]
  map_mul' b b' := by
    simp only [map_mul, map_add, Dp.κ_mul]
    linear_combination -(Dp.σ.1 (Dp.κ b) * Dp.σ.1 r * (Dp.σ.1 (Dp.κ b') * Dp.σ.1 r)) * Dp.η_sq
  map_zero' := by rw [map_zero, map_zero, Dp.κ_zero, zero_mul, map_zero, zero_mul, add_zero]
  map_add' b b' := by simp only [map_add, Dp.κ_add, add_mul]; ring
  commutes' c := by
    simp only [Dp.κ_algebraMap, zero_mul, map_zero, add_zero, AlgHom.commutes]
def fr (r : (R : Type u)) : LHom Dp.D Dp.D :=
  ⟨Dp.frAlg r, ⟨fun b hb => Dp.π.2.map_nonunit b (by
    convert hb.map Dp.π.1 using 1
    show _ = Dp.π.1 (Dp.σ.1 (Dp.π.1 b) + Dp.σ.1 (Dp.κ b * r) * Dp.η)
    rw [map_add, map_mul, Dp.π_η, mul_zero, add_zero, Dp.sect]; rfl)⟩⟩
end DualPair
section Eval
variable {M : Type u} [AddCommGroup M] [Module R₀ M]
def evalT {A : Type u} [CommRing A] [Algebra R₀ A] (H : M →ₗ[R₀] A) (K : Submodule R₀ A)
    (Y : M ⊗[R₀] K) : A :=
  LinearMap.mul' R₀ A (TensorProduct.map H K.subtype Y)
end Eval
end ReciprocityTheory.PGsh


