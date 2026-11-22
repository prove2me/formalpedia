-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_Statement
-- name    : Formalism_DoubleCosetMeasures_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:04:59.280202+00:00
-- url     : https://prove2.me/theorems/c1688393-0777-4a6f-8b2f-bfc380f3e5c8
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/Statement.lean

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
open MeasureTheory Matrix
namespace Formalism.DoubleCosetMeasures
def IntRightInv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G),
    IsOpen (K₀ : Set G) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G → E),
      (∀ g : G, ∀ k ∈ K₀, f (g * k) = f g) → HasCompactSupport f →
      (Function.support (fun x : G ⧸ K₀ => f x.out)).Finite ∧
      ∫ g, f g ∂μ = ∑ᶠ x : G ⧸ K₀, (μ (K₀ : Set G)).toReal • f x.out
def IntTwoSided : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [MeasurableSpace G₁]
    [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [MeasurableSpace G₂]
    [BorelSpace G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [μ₁.IsMulRightInvariant]
    [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂),
    IsOpen (K₁ : Set G₁) → IsOpen (K₂ : Set G₂) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G₁ × G₂ → E),
      (∀ a ∈ K₁, ∀ b ∈ K₂, ∀ x : G₁, ∀ y : G₂, f (a * x, y * b) = f (x, y)) →
      HasCompactSupport f →
      (Function.support (fun p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) =>
          f (p.1.out, p.2.out))).Finite ∧
      ∫ p, f p ∂(μ₁.prod μ₂) =
        ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
          ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • f (p.1.out, p.2.out)
def DosetVol : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G),
    IsOpen (K₀ : Set G) → IsCompact (K₀ : Set G) → ∀ g : G,
      (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 ∧
      μ (DoubleCoset.doubleCoset g (K₀ : Set G) (K₀ : Set G)) =
        ((K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ : ENNReal) * μ (K₀ : Set G)
def IntBiInv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G),
    IsOpen (K₀ : Set G) → IsCompact (K₀ : Set G) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G → E),
      (∀ a ∈ K₀, ∀ b ∈ K₀, ∀ g : G, f (a * g * b) = f g) → HasCompactSupport f →
      (Function.support (fun x : DoubleCoset.Quotient (K₀ : Set G) (K₀ : Set G) =>
          f (Quotient.out x))).Finite ∧
      ∫ g, f g ∂μ = ∑ᶠ x : DoubleCoset.Quotient (K₀ : Set G) (K₀ : Set G),
        (((K₀.map (MulAut.conj (Quotient.out x)).toMonoidHom).relIndex K₀ : ℝ) *
          (μ (K₀ : Set G)).toReal) • f (Quotient.out x)
section Mat
variable {K : Type} [CommRing K] {n : ℕ}
def IsLowUni (x : Matrix (Fin n) (Fin n) K) : Prop := x.IsLowerTriangular ∧ ∀ a, x a a = 1
def IsUpUni (x : Matrix (Fin n) (Fin n) K) : Prop := x.IsUpperTriangular ∧ ∀ a, x a a = 1
def IsInt (R : Subring K) (Z : Matrix (Fin n) (Fin n) K) : Prop := ∀ a b, Z a b ∈ R
def sLow (x : Matrix (Fin n) (Fin n) K) : K :=
  ∑ j : Fin n, if h : j.val + 1 < n then x ⟨j.val + 1, h⟩ j else 0
def sUp (u : Matrix (Fin n) (Fin n) K) : K :=
  ∑ j : Fin n, if h : j.val + 1 < n then u j ⟨j.val + 1, h⟩ else 0
end Mat
def revIn : List ℕ → ℕ → ℕ
  | [], j => j
  | a :: s, j => if j < a then a - 1 - j else a + revIn s (j - a)
def blk : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: s, j => if j < a then 0 else 1 + blk s (j - a)
def pt {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a b => if (b : ℕ) = revIn s a then ((t (blk s a) : Kˣ) : K) else 0
section Coker
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
def coeLin : (Fin n → R) →ₗ[R] (Fin n → K) :=
  LinearMap.pi (fun j => (Algebra.linearMap R K).comp (LinearMap.proj j))
def latZ (Z : Matrix (Fin n) (Fin n) K) : Submodule R (Fin n → R) :=
  Submodule.comap (coeLin R)
    (LinearMap.range ((Z.mulVecLin.restrictScalars R).comp (coeLin R)))
abbrev coker (Z : Matrix (Fin n) (Fin n) K) : Type := (Fin n → R) ⧸ latZ R Z
abbrev KR : Type := K ⧸ LinearMap.range (Algebra.linearMap R K)
def eLast : Fin n → R := fun j => if j.val + 1 = n then 1 else 0
def eZ (Z : Matrix (Fin n) (Fin n) K) : coker R Z := Submodule.Quotient.mk (eLast R)
def lastCoord : (Fin n → K) →ₗ[R] K :=
  ∑ j : Fin n, if j.val + 1 = n then (LinearMap.proj j : (Fin n → K) →ₗ[R] K) else 0
def lamLin (Z : Matrix (Fin n) (Fin n) K) : (Fin n → R) →ₗ[R] KR R :=
  (Submodule.mkQ _).comp ((lastCoord R).comp ((Z⁻¹.mulVecLin.restrictScalars R).comp (coeLin R)))
def isoSet (Z : Matrix (Fin n) (Fin n) K) (C : Type) [AddCommGroup C] [Module R C] (e : C)
    (lam : C →ₗ[R] KR R) : Set (coker R Z ≃ₗ[R] C) :=
  {φ | φ (eZ R Z) = e ∧ ∀ v : Fin n → R, lam (φ (Submodule.Quotient.mk v)) = lamLin R Z v}
end Coker
def UniGroup : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (x y : Matrix (Fin n) (Fin n) K),
    (IsLowUni x → IsLowUni y → IsLowUni (x * y)) ∧ (IsUpUni x → IsUpUni y → IsUpUni (x * y)) ∧
    (IsLowUni x → IsLowUni x⁻¹ ∧ x.det = 1) ∧ (IsUpUni x → IsUpUni x⁻¹ ∧ x.det = 1)
def SimpleAdd : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (x y : Matrix (Fin n) (Fin n) K),
    (IsLowUni x → IsLowUni y → sLow (x * y) = sLow x + sLow y) ∧
    (IsUpUni x → IsUpUni y → sUp (x * y) = sUp x + sUp y)
def IntInv : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n : ℕ) (a b Z : Matrix (Fin n) (Fin n) K),
    IsLowUni a → IsUpUni b → IsInt R a → IsInt R b → (IsInt R (a * Z * b) ↔ IsInt R Z)
def IsoInv : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n : ℕ) (a b Z : Matrix (Fin n) (Fin n) K),
    IsLowUni a → IsUpUni b → IsInt R a → IsInt R b →
    ∀ (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R),
      Nat.card (isoSet R (a * Z * b) C e lam) = Nat.card (isoSet R Z C e lam)
def PhaseWellDef : Prop :=
  ∀ (K : Type) [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) (x y : Matrix (Fin s.sum) (Fin s.sum) K),
    IsLowUni x → IsUpUni y → x * pt s t * y = pt s t → sLow x + sUp y = 0
section Groups
variable (K : Type) [CommRing K]
theorem isLowUni_mul {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x)
    (hy : IsLowUni y) : IsLowUni (x * y) := by
  refine ⟨hx.1.mul hy.1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2, hy.2, mul_one]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · exact mul_eq_zero_of_right _ (hy.1 (OrderDual.toDual_lt_toDual.2 h))
    · exact mul_eq_zero_of_left (hx.1 (OrderDual.toDual_lt_toDual.2 h)) _
  · intro h; exact absurd (Finset.mem_univ a) h
theorem isUpUni_mul {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x)
    (hy : IsUpUni y) : IsUpUni (x * y) := by
  refine ⟨hx.1.mul hy.1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2, hy.2, mul_one]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · exact mul_eq_zero_of_left (hx.1 h) _
    · exact mul_eq_zero_of_right _ (hy.1 h)
  · intro h; exact absurd (Finset.mem_univ a) h
theorem isLowUni_det {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) : x.det = 1 := by
  rw [Matrix.det_of_lowerTriangular x hx.1]
  simp [hx.2]
theorem isUpUni_det {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) : x.det = 1 := by
  rw [Matrix.det_of_upperTriangular hx.1]
  simp [hx.2]
theorem isLowUni_inv {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) :
    IsLowUni x⁻¹ := by
  have hu : IsUnit x.det := by rw [isLowUni_det K hx]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet x hu
  have hT : x⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  refine ⟨hT, fun a => ?_⟩
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul x hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · exact mul_eq_zero_of_right _ (hx.1 (OrderDual.toDual_lt_toDual.2 h'))
    · exact mul_eq_zero_of_left (hT (OrderDual.toDual_lt_toDual.2 h')) _
  · intro h'; exact absurd (Finset.mem_univ a) h'
theorem isUpUni_inv {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) :
    IsUpUni x⁻¹ := by
  have hu : IsUnit x.det := by rw [isUpUni_det K hx]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet x hu
  have hT : x⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  refine ⟨hT, fun a => ?_⟩
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul x hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · exact mul_eq_zero_of_left (hT h') _
    · exact mul_eq_zero_of_right _ (hx.1 h')
  · intro h'; exact absurd (Finset.mem_univ a) h'
theorem isLowUni_one {n : ℕ} : IsLowUni (1 : Matrix (Fin n) (Fin n) K) := ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
theorem isUpUni_one {n : ℕ} : IsUpUni (1 : Matrix (Fin n) (Fin n) K) := ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
def lowUniG (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | IsLowUni (g : Matrix (Fin n) (Fin n) K)}
  one_mem' := by simpa using isLowUni_one K
  mul_mem' := by intro a b ha hb; simpa using isLowUni_mul K ha hb
  inv_mem' := by intro a ha; simpa [Matrix.coe_units_inv] using isLowUni_inv K ha
def upUniG (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | IsUpUni (g : Matrix (Fin n) (Fin n) K)}
  one_mem' := by simpa using isUpUni_one K
  mul_mem' := by intro a b ha hb; simpa using isUpUni_mul K ha hb
  inv_mem' := by intro a ha; simpa [Matrix.coe_units_inv] using isUpUni_inv K ha
def lowW (s : List ℕ) (t : ℕ → Kˣ) : Subgroup (GL (Fin s.sum) K) where
  carrier := {g | IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧
    ∃ h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni h ∧ (g : Matrix _ _ K) * pt s t = pt s t * h}
  one_mem' := ⟨by simpa using isLowUni_one K, 1, isLowUni_one K, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, h₁, hh₁, e₁⟩ ⟨hb, h₂, hh₂, e₂⟩
    refine ⟨by simpa using isLowUni_mul K ha hb, h₁ * h₂, isLowUni_mul K hh₁ hh₂, ?_⟩
    simp only [Units.val_mul]
    rw [Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨ha, h, hh, e⟩
    refine ⟨by simpa [Matrix.coe_units_inv] using isLowUni_inv K ha, h⁻¹, isLowUni_inv K hh, ?_⟩
    have hdet : IsUnit h.det := by simp [isLowUni_det K hh]
    have hadet : IsUnit (a : Matrix (Fin s.sum) (Fin s.sum) K).det := by
      simp [isLowUni_det K ha]
    simp only [Matrix.coe_units_inv]
    calc (a : Matrix _ _ K)⁻¹ * pt s t
        = (a : Matrix _ _ K)⁻¹ * pt s t * (h * h⁻¹) := by
          rw [Matrix.mul_nonsing_inv h hdet, Matrix.mul_one]
      _ = (a : Matrix _ _ K)⁻¹ * ((a : Matrix _ _ K) * pt s t) * h⁻¹ := by
          rw [e]; simp only [Matrix.mul_assoc]
      _ = pt s t * h⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hadet, Matrix.one_mul]
variable {K}
def intSub (R : Subring K) {n : ℕ} (H : Subgroup (GL (Fin n) K)) : Subgroup H where
  carrier := {g | IsInt R ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
    IsInt R (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  one_mem' := by
    constructor <;> intro a b <;> by_cases h : a = b <;> simp [h, R.one_mem, R.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    constructor
    · intro a b
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact R.sum_mem fun k _ => R.mul_mem (hx a k) (hy k b)
    · intro a b
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact R.sum_mem fun k _ => R.mul_mem (hy' a k) (hx' k b)
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩
end Groups
section Integral
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
instance instMeasGL (n : ℕ) : MeasurableSpace (GL (Fin n) K) := borel _
instance instBorelGL (n : ℕ) : BorelSpace (GL (Fin n) K) := ⟨rfl⟩
open Classical in

def phi (R : Subring K) (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (C : Type) [AddCommGroup C]
    [Module R C] (e : C) (lam : C →ₗ[R] KR R) (p : lowW K s t × upUniG K s.sum) : ℂ :=
  (if IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))
    then (Nat.card (isoSet R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) C e lam) : ℂ) else 0) *
    ψ (sLow ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))
def BB (R : Subring K) (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (C : Type) [AddCommGroup C]
    [Module R C] (e : C) (lam : C →ₗ[R] KR R) (μ₁ : Measure (lowW K s t))
    (μ₂ : Measure (upUniG K s.sum)) : ℂ :=
  ∫ p, phi R s t ψ C e lam p ∂(μ₁.prod μ₂)
end Integral
def BBFinite : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsOpen (R : Set K) → ∀ (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ), (∀ r ∈ R, ψ r = 1) →
    ∀ (μ₁ : Measure (lowW K s t)) (μ₂ : Measure (upUniG K s.sum)) [μ₁.IsMulRightInvariant]
      [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂] (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R),
      HasCompactSupport (phi R s t ψ C e lam) →
      (Function.support (fun p : Quotient (QuotientGroup.rightRel (intSub R (lowW K s t))) ×
          (upUniG K s.sum ⧸ intSub R (upUniG K s.sum)) =>
          phi R s t ψ C e lam (p.1.out, p.2.out))).Finite ∧
      BB R s t ψ C e lam μ₁ μ₂ =
        ∑ᶠ p : Quotient (QuotientGroup.rightRel (intSub R (lowW K s t))) ×
            (upUniG K s.sum ⧸ intSub R (upUniG K s.sum)),
          (((μ₁ (intSub R (lowW K s t) : Set (lowW K s t))).toReal *
            (μ₂ (intSub R (upUniG K s.sum) : Set (upUniG K s.sum))).toReal : ℝ) : ℂ) *
            phi R s t ψ C e lam (p.1.out, p.2.out)
def BBNorm : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsOpen (R : Set K) → ∀ (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ), (∀ r ∈ R, ψ r = 1) →
    ∀ (μ₁ : Measure (lowW K s t)) (μ₂ : Measure (upUniG K s.sum)) [μ₁.IsMulRightInvariant]
      [μ₂.IsMulLeftInvariant] [SFinite μ₁] [SFinite μ₂],
      μ₁ (intSub R (lowW K s t) : Set (lowW K s t)) = 1 →
      μ₂ (intSub R (upUniG K s.sum) : Set (upUniG K s.sum)) = 1 →
      ∀ (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R),
      HasCompactSupport (phi R s t ψ C e lam) →
      BB R s t ψ C e lam μ₁ μ₂ =
        ∑ᶠ p : Quotient (QuotientGroup.rightRel (intSub R (lowW K s t))) ×
            (upUniG K s.sum ⧸ intSub R (upUniG K s.sum)), phi R s t ψ C e lam (p.1.out, p.2.out)
def SuppCompact : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] (R : Subring K),
    IsOpen (R : Set K) → IsCompact (R : Set K) → ∀ (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ)
      (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R),
      HasCompactSupport (phi R s t ψ C e lam)
def SectionBij : Prop :=
  ∀ (K : Type) [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) (x y : Matrix (Fin s.sum) (Fin s.sum) K),
    IsLowUni x → IsUpUni y →
    ∃! p : Matrix (Fin s.sum) (Fin s.sum) K × Matrix (Fin s.sum) (Fin s.sum) K,
      (IsLowUni p.1 ∧ ∃ h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni h ∧ p.1 * pt s t = pt s t * h) ∧
      IsUpUni p.2 ∧ p.1 * pt s t * p.2 = x * pt s t * y
def latOf {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (g : GL (Fin n) K) :
    Submodule R (Fin n → K) :=
  Submodule.map (((g : Matrix (Fin n) (Fin n) K).mulVecLin.restrictScalars R).comp (coeLin R)) ⊤
def LatticeCoset : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K) (n : ℕ) (g h : GL (Fin n) K),
    latOf R g = latOf R h ↔
      (IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) ∧
        IsInt R (((h⁻¹ * g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K))
def IsoFinite : Prop :=
  ∀ (K : Type) [CommRing K] (R : Subring K),
    (∀ d : R, IsUnit (d : K) → Finite (R ⧸ Ideal.span {d})) →
    ∀ (n : ℕ) (Z : Matrix (Fin n) (Fin n) K), IsInt R Z → IsUnit Z.det →
    Finite (coker R Z) ∧
    ∀ (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R),
      (isoSet R Z C e lam).Finite
def HaarExists : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [LocallyCompactSpace K] (R : Subring K), IsOpen (R : Set K) → IsCompact (R : Set K) →
    (∃ ϖ : Kˣ, (ϖ : K) ∈ R ∧ ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) →
    ∀ (s : List ℕ) (t : ℕ → Kˣ),
      (∃ μ₁ : Measure (lowW K s t), μ₁.IsMulLeftInvariant ∧ μ₁.IsMulRightInvariant ∧
        SFinite μ₁ ∧ μ₁ (intSub R (lowW K s t) : Set (lowW K s t)) = 1) ∧
      (∃ μ₂ : Measure (upUniG K s.sum), μ₂.IsMulLeftInvariant ∧ μ₂.IsMulRightInvariant ∧
        SFinite μ₂ ∧ μ₂ (intSub R (upUniG K s.sum) : Set (upUniG K s.sum)) = 1)
end Formalism.DoubleCosetMeasures


