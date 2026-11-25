-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:57.075146+00:00
-- url     : https://prove2.me/theorems/5fee12f3-d7a8-5944-90a2-96ea5143ebf0
-- title:
--   Exists Not Cong Pow
-- statement:
--   Definitions and structural lemmas for Exists Not Cong Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ExistsNotCongPow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_exists_isFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
section Cong
variable {A : ValuationSubring Ω}
theorem cong_symm {x y : Ω} (h : A.valuation (x - y) < 1) : A.valuation (y - x) < 1 := by
  rwa [Valuation.map_sub_swap]
theorem cong_trans {x y z : Ω} (h : A.valuation (x - y) < 1) (h' : A.valuation (y - z) < 1) :
    A.valuation (x - z) < 1 := by
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]; exact Valuation.map_add_lt _ h h'
theorem val_pow_le_one {x : Ω} (hx : A.valuation x ≤ 1) (n : ℕ) : A.valuation (x ^ n) ≤ 1 := by
  rw [map_pow]; exact pow_le_one₀ zero_le hx
theorem cong_pow {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (n : ℕ) : A.valuation (x ^ n - y ^ n) < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_pow_le_one hy n)) h
theorem val_apply_le_one {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 := by
  rw [A.valuation_le_one_iff] at hx ⊢
  exact (apply_mem_iff_of_mem_Dec hσ x).mpr hx
theorem exists_not_cong_pow [IsAlgClosed Ω] {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    ∃ x : Ω, A.valuation x ≤ 1 ∧ ¬ A.valuation (x ^ m - x ^ n) < 1 := by
  have hdeg : (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω).degree = m := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rw [Polynomial.degree_X_pow, ← Polynomial.C_1, Polynomial.degree_X_pow_add_C hn]
    exact_mod_cast hmn
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω)
    (by rw [hdeg]; exact_mod_cast (hn.trans hmn).ne')
  have hx' : x ^ m = x ^ n + 1 := by
    have := hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  refine ⟨x, ?_, ?_⟩
  · by_contra hc
    have h1 : 1 < A.valuation x := not_le.mp hc
    have h2 : A.valuation (x ^ n + 1) < A.valuation x ^ m := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_pow]; exact pow_lt_pow_right₀ h1 hmn
      · rw [map_one]; exact one_lt_pow₀ h1 (hn.trans hmn).ne'
    rw [← hx', map_pow] at h2
    exact lt_irrefl _ h2
  · rw [hx', add_sub_cancel_left, map_one]; exact lt_irrefl _
end Cong
def ActsAs (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (a b : ℕ) : Prop :=
  σ ∈ Dec (F := E) A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((σ x) ^ (q ^ b) - x ^ (q ^ a)) < 1
section ActsAs
variable {A : ValuationSubring Ω} {q : ℕ}
theorem ActsAs.mul {σ τ : G E Ω} {a b c d : ℕ} (hσ : ActsAs A q σ a b) (hτ : ActsAs A q τ c d) :
    ActsAs A q (σ * τ) (a + c) (b + d) := by
  refine ⟨(Dec (F := E) A).mul_mem hσ.1 hτ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one hτ.1 hx
  have h1 := cong_pow (val_pow_le_one (val_apply_le_one hσ.1 hy) _) (val_pow_le_one hy _)
    (hσ.2 _ hy) (q ^ d)
  have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (hτ.2 _ hx) (q ^ a)
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at h1 h2
  rw [add_comm d a, add_comm c a] at h2
  exact cong_trans h1 h2
theorem ActsAs.inv {σ : G E Ω} {a b : ℕ} (hσ : ActsAs A q σ a b) : ActsAs A q σ⁻¹ b a := by
  refine ⟨(Dec (F := E) A).inv_mem hσ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one ((Dec (F := E) A).inv_mem hσ.1) hx
  have h1 := hσ.2 _ hy
  rw [mul_inv_apply] at h1
  exact cong_symm h1
theorem actsAs_zero_iff {σ : G E Ω} : ActsAs A q σ 0 0 ↔ σ ∈ Ine (F := E) A := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl
theorem actsAs_one_iff {σ : G E Ω} : ActsAs A q σ 1 0 ↔ IsFrob A q σ := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl
theorem ActsAs.unique [IsAlgClosed Ω] (hq : 1 < q) {σ : G E Ω} {a b c d : ℕ}
    (h : ActsAs A q σ a b) (h' : ActsAs A q σ c d) : (a : ℤ) - b = (c : ℤ) - d := by
  have h1 := h.inv.mul h'
  rw [inv_mul_cancel] at h1
  have key : ∀ m n : ℕ, ActsAs A q (1 : G E Ω) m n → ¬ n < m := by
    intro m n hmn hlt
    obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (pow_pos (zero_lt_one.trans hq) n)
      (pow_lt_pow_right₀ hq hlt)
    exact hx' (cong_symm (hmn.2 x hx))
  have k1 := key _ _ h1
  have k2 := key _ _ (by simpa using h1.inv)
  omega
theorem ActsAs.cancel {φ : G E Ω} (hφ : IsFrob A q φ) {σ : G E Ω} {a b : ℕ} (n : ℕ)
    (h : ActsAs A q σ (a + n) (b + n)) : ActsAs A q σ a b := by
  induction n with
  | zero => exact h
  | succ n ih =>
    refine ih ⟨h.1, fun x hx => ?_⟩
    have h1 := h.2 x hx
    rw [← add_assoc, ← add_assoc, pow_succ, pow_succ, pow_mul, pow_mul] at h1
    have hu := val_pow_le_one (val_apply_le_one h.1 hx) (q ^ (b + n))
    have hv := val_pow_le_one hx (q ^ (a + n))
    rw [← valuation_apply_lt_one_iff hφ.1, map_sub]
    exact cong_trans (cong_trans (hφ.2 _ hu) h1) (cong_symm (hφ.2 _ hv))
end ActsAs
def weilSub (A : ValuationSubring Ω) (q : ℕ) : Subgroup (G E Ω) where
  carrier := {σ | ∃ a b, ActsAs A q σ a b}
  one_mem' := ⟨0, 0, actsAs_zero_iff.mpr (Ine (F := E) A).one_mem⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, h⟩ ⟨c, d, h'⟩
    exact ⟨_, _, h.mul h'⟩
  inv_mem' := by
    rintro σ ⟨a, b, h⟩
    exact ⟨_, _, h.inv⟩
theorem one_lt_normV (w : HeightOneSpectrum (𝓞 E)) : 1 < normV w := by
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  exact Finite.one_lt_card
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
def Weil (_h : IsPlaceOver A w) : Subgroup (G E Ω) := weilSub A (normV w)
variable (h : IsPlaceOver A w)
theorem Ine_le_Weil : Ine (F := E) A ≤ Weil h := fun _ hσ => ⟨0, 0, actsAs_zero_iff.mpr hσ⟩
theorem mem_Weil_of_isFrob {σ : G E Ω} (hσ : IsFrob A (normV w) σ) : σ ∈ Weil h :=
  ⟨1, 0, actsAs_one_iff.mpr hσ⟩
def ineIncl : Ine (F := E) A →* Weil h := Subgroup.inclusion (Ine_le_Weil h)
@[simp] theorem coe_ineIncl (σ : Ine (F := E) A) : (ineIncl h σ : G E Ω) = σ := rfl
variable {h}
def deg (σ : Weil h) : ℤ :=
  (σ.2.choose : ℤ) - (σ.2.choose_spec.choose : ℤ)
variable [IsAlgClosure E Ω]
theorem deg_eq {σ : Weil h} {a b : ℕ} (hσ : ActsAs A (normV w) (σ : G E Ω) a b) :
    deg σ = (a : ℤ) - b :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  ActsAs.unique (one_lt_normV w) σ.2.choose_spec.choose_spec hσ
@[simp] theorem deg_mul (σ τ : Weil h) : deg (σ * τ) = deg σ + deg τ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  obtain ⟨c, d, hτ⟩ := τ.2
  rw [deg_eq hσ, deg_eq hτ, deg_eq (σ := σ * τ) (hσ.mul hτ)]
  push_cast; ring
@[simp] theorem deg_one : deg (1 : Weil h) = 0 := by
  have := deg_mul (1 : Weil h) 1
  rw [mul_one] at this; omega
@[simp] theorem deg_inv (σ : Weil h) : deg σ⁻¹ = -deg σ := by
  have := deg_mul σ σ⁻¹
  rw [mul_inv_cancel, deg_one] at this; omega
variable (h) in

def degHom : Weil h →* Multiplicative ℤ where
  toFun σ := Multiplicative.ofAdd (deg σ)
  map_one' := by simp
  map_mul' σ τ := by simp [ofAdd_add]
@[simp] theorem degHom_apply (σ : Weil h) : degHom h σ = Multiplicative.ofAdd (deg σ) := rfl
@[simp] theorem deg_zpow (σ : Weil h) (n : ℤ) : deg (σ ^ n) = n * deg σ := by
  have := congrArg Multiplicative.toAdd (map_zpow (degHom h) σ n)
  simpa using this
@[simp] theorem deg_pow (σ : Weil h) (n : ℕ) : deg (σ ^ n) = n * deg σ := by
  rw [← zpow_natCast, deg_zpow]
theorem actsAs_of_deg {σ : Weil h} {a b : ℕ} (hσ : deg σ = (a : ℤ) - b) :
    ActsAs A (normV w) (σ : G E Ω) a b := by
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  obtain ⟨c, d, hcd⟩ := σ.2
  rw [deg_eq hcd] at hσ
  have h1 : ActsAs A (normV w) (1 : G E Ω) b b := ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
  have h2 := hcd.mul h1
  rw [mul_one, show c + b = a + d by omega, add_comm d b] at h2
  exact ActsAs.cancel hφ d h2
theorem deg_eq_zero_iff {σ : Weil h} : deg σ = 0 ↔ (σ : G E Ω) ∈ Ine (F := E) A :=
  ⟨fun hσ => actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_zero_iff.mpr hσ)⟩
theorem deg_eq_one_iff {σ : Weil h} : deg σ = 1 ↔ IsFrob A (normV w) (σ : G E Ω) :=
  ⟨fun hσ => actsAs_one_iff.mp (actsAs_of_deg (a := 1) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_one_iff.mpr hσ)⟩
variable (h) in

def frob : Weil h := ⟨(exists_isFrob h).choose, mem_Weil_of_isFrob h (exists_isFrob h).choose_spec⟩
theorem isFrob_frob : IsFrob A (normV w) (frob h : G E Ω) := (exists_isFrob h).choose_spec
@[simp] theorem deg_frob : deg (frob h) = 1 := deg_eq_one_iff.mpr isFrob_frob
variable (h) in

def unrChar (c : ℂˣ) : Weil h →* ℂˣ := (zpowersHom ℂˣ c).comp (degHom h)
variable (w) in

def qPow (s : ℝ) : ℂˣ :=
  Units.mk0 (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))
example : (frob h : G E Ω) ∉ Ine (F := E) A := by
  rw [← deg_eq_zero_iff, deg_frob]; exact one_ne_zero
example : deg (frob h)⁻¹ = -1 := by simp
end GlobalTheory.WeilDeligne


