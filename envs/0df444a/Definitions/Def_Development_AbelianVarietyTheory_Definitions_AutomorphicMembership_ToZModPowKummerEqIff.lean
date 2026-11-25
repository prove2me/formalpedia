-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:58.274729+00:00
-- url     : https://prove2.me/theorems/4deccf12-1441-57f1-b857-49bd242f4930
-- title:
--   To ZMod Pow Kummer Eq Iff
-- statement:
--   Definitions and structural lemmas for To ZMod Pow Kummer Eq Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_Weil_le_Dec
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_cycZ_toZModPow_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
namespace GlobalTheory.WeilDeligne
section Roots
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
def rootSeq (a : Ω) (n : ℕ) : Ω :=
  Nat.rec a (fun _ y => (IsAlgClosed.exists_pow_nat_eq y (Fact.out : l.Prime).pos).choose) n
@[simp] theorem rootSeq_zero (a : Ω) : rootSeq l a 0 = a := rfl
theorem rootSeq_succ_pow (a : Ω) (n : ℕ) : rootSeq l a (n + 1) ^ l = rootSeq l a n :=
  (IsAlgClosed.exists_pow_nat_eq (rootSeq l a n) (Fact.out : l.Prime).pos).choose_spec
theorem rootSeq_pow (a : Ω) (n : ℕ) : rootSeq l a n ^ l ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, rootSeq_succ_pow, ih]
variable (Ω) [CharZero Ω]
theorem exists_unitySeq : ∃ z : ℕ → Ω, (∀ n, IsPrimitiveRoot (z n) (l ^ n)) ∧
    ∀ n, z (n + 1) ^ l = z n := by
  have hl : l.Prime := Fact.out
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  refine ⟨fun n => Nat.casesOn n 1 (rootSeq l ζ), fun n => ?_, fun n => ?_⟩
  · cases n with
    | zero => simp
    | succ n =>
      have h := orderOf_eq_prime_pow (x := rootSeq l ζ n) (p := l) (n := n)
        (by rw [rootSeq_pow]; exact hζ.ne_one hl.one_lt)
        (by rw [pow_succ, pow_mul, rootSeq_pow, hζ.pow_eq_one])
      rw [← h]
      exact IsPrimitiveRoot.orderOf _
  · cases n with
    | zero => exact hζ.pow_eq_one
    | succ n => exact rootSeq_succ_pow l ζ n
def unitySeq : ℕ → Ω := (exists_unitySeq Ω l).choose
theorem unitySeq_primitive (n : ℕ) : IsPrimitiveRoot (unitySeq Ω l n) (l ^ n) :=
  (exists_unitySeq Ω l).choose_spec.1 n
theorem unitySeq_succ_pow (n : ℕ) : unitySeq Ω l (n + 1) ^ l = unitySeq Ω l n :=
  (exists_unitySeq Ω l).choose_spec.2 n
theorem unitySeq_pow_eq_iff (n a b : ℕ) :
    unitySeq Ω l n ^ a = unitySeq Ω l n ^ b ↔ (a : ZMod (l ^ n)) = b := by
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hζ := unitySeq_primitive Ω l n
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [ZMod.natCast_eq_natCast_iff, hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
  simp
def unityPow (n : ℕ) (c : ℤ_[l]) : Ω := unitySeq Ω l n ^ (PadicInt.toZModPow n c).val
theorem unityPow_eq_pow_iff {n k : ℕ} {c : ℤ_[l]} :
    unityPow Ω l n c = unitySeq Ω l n ^ k ↔ PadicInt.toZModPow n c = k := by
  rw [unityPow, unitySeq_pow_eq_iff, ZMod.natCast_zmod_val]
theorem unityPow_add (n : ℕ) (c d : ℤ_[l]) :
    unityPow Ω l n (c + d) = unityPow Ω l n c * unityPow Ω l n d := by
  conv_rhs => rw [unityPow, unityPow, ← pow_add]
  rw [unityPow_eq_pow_iff]; simp
theorem unityPow_mul (n : ℕ) (c d : ℤ_[l]) :
    unityPow Ω l n (c * d) = unityPow Ω l n d ^ (PadicInt.toZModPow n c).val := by
  conv_rhs => rw [unityPow, ← pow_mul]
  rw [unityPow_eq_pow_iff]; simp [mul_comm]
theorem unityPow_pow (n : ℕ) (c : ℤ_[l]) : unityPow Ω l n c ^ l ^ n = 1 := by
  rw [unityPow, ← pow_mul, mul_comm, pow_mul, (unitySeq_primitive Ω l n).pow_eq_one, one_pow]
variable {Ω} in

theorem existsUnique_unityPow {y : ℕ → Ω} (h0 : ∀ n, y n ^ l ^ n = 1)
    (hy : ∀ n, y (n + 1) ^ l = y n) : ∃! c : ℤ_[l], ∀ n, y n = unityPow Ω l n c := by
  have : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  choose k _ hk using fun n => (unitySeq_primitive Ω l n).eq_pow_of_pow_eq_one (h0 n)
  have h3 : ∀ n, (l : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, sub_eq_zero, ← unitySeq_pow_eq_iff Ω, hk, ← hy, ← hk, ← pow_mul, mul_comm,
      pow_mul, unitySeq_succ_pow]
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3), fun n => ?_,
    fun c hc => PadicInt.ext_of_toZModPow.mp fun n => ?_⟩
  · rw [← hk, eq_comm, unityPow_eq_pow_iff,
      PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3 n, Int.cast_natCast]
  · rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3 n, Int.cast_natCast,
      ← unityPow_eq_pow_iff Ω, ← hc, hk]
end Roots
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
section Kummer
variable (l : ℕ) [Fact l.Prime]
variable (E Ω) in

def zetaPow (n : ℕ) (c : ℤ_[l]) : Ω :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  unityPow Ω l n c
variable (Ω) in

def rootOf (a : E) (n : ℕ) : Ω :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rootSeq l (algebraMap E Ω a) n
omit [NumberField E] in

theorem rootOf_pow (a : E) (n : ℕ) : rootOf Ω l a n ^ l ^ n = algebraMap E Ω a :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rootSeq_pow l _ n
omit [NumberField E] in

theorem rootOf_ne_zero {a : E} (ha : a ≠ 0) (n : ℕ) : rootOf Ω l a n ≠ 0 := by
  intro h0
  have := rootOf_pow (Ω := Ω) l a n
  rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at this
  exact ha ((map_eq_zero _).mp this.symm)
theorem existsUnique_kummer (a : Eˣ) (σ : G E Ω) :
    ∃! c : ℤ_[l], ∀ n, σ (rootOf Ω l (a : E) n) = zetaPow E Ω l n c * rootOf Ω l (a : E) n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have h := existsUnique_unityPow l (y := fun n => σ (rootOf Ω l (a : E) n) / rootOf Ω l (a : E) n)
    (fun n => by
      rw [div_pow, ← map_pow, rootOf_pow, AlgEquiv.commutes, div_self (by simp)])
    (fun n => by
      rw [div_pow, ← map_pow]
      exact congrArg (fun x => σ x / x) (rootSeq_succ_pow l _ n))
  have e : ∀ n y z : Ω, z ≠ 0 → (y / z = n ↔ y = n * z) := fun _ _ _ hz => div_eq_iff hz
  simp only [e _ _ _ (rootOf_ne_zero l a.ne_zero _)] at h
  exact h
def kummer (a : Eˣ) (σ : G E Ω) : ℤ_[l] := (existsUnique_kummer l a σ).exists.choose
theorem kummer_spec (a : Eˣ) (σ : G E Ω) (n : ℕ) :
    σ (rootOf Ω l (a : E) n) = zetaPow E Ω l n (kummer l a σ) * rootOf Ω l (a : E) n :=
  (existsUnique_kummer l a σ).exists.choose_spec n
theorem apply_zetaPow (σ : G E Ω) (n : ℕ) (c : ℤ_[l]) :
    σ (zetaPow E Ω l n c) = zetaPow E Ω l n ((cycZ E Ω l σ : ℤ_[l]ˣ) * c) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact (cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G E Ω) Ω σ) _
    (unityPow_pow Ω l n c)).trans (unityPow_mul Ω l n _ c).symm
theorem kummer_mul (a : Eˣ) (σ τ : G E Ω) :
    kummer l a (σ * τ) = kummer l a σ + (cycZ E Ω l σ : ℤ_[l]ˣ) * kummer l a τ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  refine (existsUnique_kummer l a (σ * τ)).unique (kummer_spec l a _) fun n => ?_
  rw [AlgEquiv.mul_apply, kummer_spec, map_mul, apply_zetaPow, kummer_spec, ← mul_assoc, add_comm]
  congr 1
  exact (unityPow_add Ω l n _ _).symm
@[simp] theorem kummer_one (a : Eˣ) : kummer l a (1 : G E Ω) = 0 := by
  simpa using kummer_mul l a (1 : G E Ω) 1
end Kummer
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
theorem cycZ_of_mem_Ine (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) A) : cycZ E Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp
def ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) : Ine (F := E) A :=
  ⟨(g : G E Ω) * σ * (g : G E Ω)⁻¹, conj_mem_Ine (Weil_le_Dec h g.2) σ.2⟩
omit [IsAlgClosure E Ω] in

@[simp] theorem ineIncl_ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) :
    ineIncl h (ineConj g σ) = g * ineIncl h σ * g⁻¹ := rfl
omit [IsAlgClosure E Ω] in

@[simp] theorem coe_ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) :
    (ineConj g σ : G E Ω) = (g : G E Ω) * σ * (g : G E Ω)⁻¹ := rfl
def kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ) :
    Ine (F := E) A →* Multiplicative ℤ_[l] :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (kummer l a (σ : G E Ω))) fun σ τ => by
    rw [Subgroup.coe_mul, kummer_mul, cycZ_of_mem_Ine h hl σ.2, Units.val_one, one_mul, ofAdd_add]
@[simp] theorem toAdd_kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    (σ : Ine (F := E) A) : (kummerChar h hl a σ).toAdd = kummer l a (σ : G E Ω) := rfl
omit [IsAlgClosure E Ω] in
variable (w) in

theorem exists_uniformiser : ∃ ϖ : 𝓞 E, ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 := by
  simpa using Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
variable (w) in

def unif : 𝓞 E := (exists_uniformiser w).choose
theorem unif_notMem : unif w ∉ w.asIdeal ^ 2 := (exists_uniformiser w).choose_spec.2
variable (w) in

def unifUnit : Eˣ := Units.mk0 ((unif w : 𝓞 E) : E) fun h0 =>
  unif_notMem (w := w) (by rw [RingOfIntegers.coe_eq_zero_iff.mp h0]; exact zero_mem _)
def tameL (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) :
    Ine (F := E) A →* Multiplicative ℤ_[l] := kummerChar h hl (unifUnit w)
end GlobalTheory.WeilDeligne


