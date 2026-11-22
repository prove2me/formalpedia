-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Words_Periods
-- name    : LeanPool_DeciSigma1_Words_Periods
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:48.817622+00:00
-- url     : https://prove2.me/theorems/e05d8b46-004d-413e-a77e-a5be9db124dc
-- title:
--   Periods
-- statement:
--   Definitions and structural lemmas for Periods, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Words
variable {α : Type*}
section Powers
variable {μ π u w : List α} {p q n : ℕ}
def pow (μ : List α) : ℕ → List α
  | 0 => []
  | n + 1 => μ ++ pow μ n
@[simp] theorem pow_zero (μ : List α) : pow μ 0 = [] := rfl
@[simp] theorem pow_succ (μ : List α) (n : ℕ) : pow μ (n + 1) = μ ++ pow μ n := rfl
@[simp] theorem length_pow (μ : List α) (n : ℕ) : (pow μ n).length = n * μ.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]
@[simp] theorem pow_nil (n : ℕ) : pow ([] : List α) n = [] := by
  induction n <;> simp_all
theorem prefix_append_of_prefix_pow (n : ℕ) (h : π <+: pow μ n) : π <+: μ ++ π := by
  induction n generalizing π with
  | zero => simp only [pow_zero, List.prefix_nil] at h; simp [h]
  | succ n ih =>
    rw [pow_succ] at h
    by_cases hlen : π.length ≤ μ.length
    · exact ((List.isPrefix_append_of_length hlen).mp h).trans (List.prefix_append _ _)
    · have hμ : μ <+: π :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) h (by omega)
      obtain ⟨τ, rfl⟩ := hμ
      rw [List.prefix_append_right_inj] at h
      simpa only [List.append_assoc, List.prefix_append_right_inj] using ih h
theorem hasPeriod_pow (u : List α) (n : ℕ) : (pow u n).HasPeriod u.length := by
  cases n with
  | zero => simp
  | succ n =>
    change pow u (n + 1) <+: (pow u (n + 1)).take u.length ++ pow u (n + 1)
    rw [pow_succ, List.take_left]
    exact prefix_append_of_prefix_pow (n + 1) List.prefix_rfl
theorem getElem?_pow (hu : u ≠ []) (hi : n < (pow u q).length) :
    (pow u q)[n]? = u[n % u.length]? := by
  rw [← (hasPeriod_pow u q).getElem?_mod u.length n (pow u q) hi]
  cases q with
  | zero => simp at hi
  | succ q =>
    exact List.getElem?_append_left (Nat.mod_lt _ (List.length_pos_iff.mpr hu))
end Powers
instance hasPeriodDecidable [DecidableEq α] (w : List α) (p : ℕ) : Decidable (w.HasPeriod p) :=
  inferInstanceAs (Decidable (w <+: _))
theorem exists_pos_period (w : List α) : ∃ p, 0 < p ∧ w.HasPeriod p :=
  ⟨w.length + 1, Nat.succ_pos _, List.hasPeriod_of_length_le w _ (Nat.le_succ _)⟩
def leastPeriod [DecidableEq α] (w : List α) : ℕ := Nat.find (exists_pos_period w)
section LeastPeriod
variable [DecidableEq α] {w : List α} {p g : ℕ}
end LeastPeriod
def PeriodicOn (w : List α) (d s e : ℕ) : Prop := ∀ p, s ≤ p → p + d < e → w[p]? = w[p + d]?
namespace PeriodicOn
variable {w : List α} {d s e : ℕ}
end PeriodicOn
def IsPrimitive (ρ : List α) : Prop := ρ ≠ [] ∧ ∀ (u : List α) (m : ℕ), ρ = pow u m → m = 1
theorem hasPeriod_iff_cyclic {ρ : List α} {p : ℕ} (hn : 0 < ρ.length) (hp : p ∣ ρ.length) :
    ρ.HasPeriod p ↔ ∀ i, ρ[i % ρ.length]? = ρ[(i + p) % ρ.length]? := by
  constructor
  · intro h i
    rw [List.hasPeriod_iff_forall_getElem?_mod] at h
    rw [h _ (Nat.mod_lt _ hn), h _ (Nat.mod_lt _ hn)]
    congr 1
    obtain ⟨c, hc⟩ := hp
    rw [hc, Nat.mod_mul_right_mod, Nat.mod_mul_right_mod, Nat.add_mod_right]
  · intro h
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    have := h i
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
theorem isPrimitive_iff_period {ρ : List α} : IsPrimitive ρ ↔
    ρ ≠ [] ∧ ∀ p, 0 < p → p < ρ.length → p ∣ ρ.length → ¬ ρ.HasPeriod p := by
  constructor
  · rintro ⟨hne, hpow⟩
    refine ⟨hne, fun p hp hpn hdvd hper => ?_⟩
    obtain ⟨m, hm⟩ := hdvd
    have hu : ρ.take p ≠ [] := by
      intro h; rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · exact hne h
    have hlen' : (pow (ρ.take p) m).length = ρ.length := by
      rw [length_pow, List.length_take, min_eq_left hpn.le,
        hm, mul_comm]
    have hρ : ρ = pow (ρ.take p) m := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < ρ.length
      · rw [getElem?_pow hu (by omega),
          List.length_take, min_eq_left hpn.le, List.getElem?_take_of_lt (Nat.mod_lt _ hp)]
        exact ((hper.getElem?_mod p i ρ hi)).symm
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have := hpow _ _ hρ
    subst this
    omega
  · rintro ⟨hne, hper⟩
    refine ⟨hne, fun u m hρ => ?_⟩
    have hlen : ρ.length = m * u.length := by
      rw [hρ, length_pow]
    rcases m with _ | _ | m
    · exfalso; apply hne; rw [hρ]; rfl
    · rfl
    · exfalso
      have hu : 0 < u.length := by
        rcases Nat.eq_zero_or_pos u.length with h | h
        · exfalso; apply hne; rw [List.length_eq_zero_iff.mp h] at hρ
          rw [hρ, pow_nil]
        · exact h
      apply hper u.length hu (by rw [hlen]; nlinarith) ⟨m + 2, by rw [hlen, mul_comm]⟩
      rw [hρ]
      exact hasPeriod_pow u _
instance isPrimitiveDecidable [DecidableEq α] : DecidablePred (IsPrimitive (α := α)) :=
  fun ρ => decidable_of_iff (ρ ≠ [] ∧ ∀ p < ρ.length, 0 < p → p ∣ ρ.length → ¬ ρ.HasPeriod p)
    (by rw [isPrimitive_iff_period]
        exact and_congr_right fun _ =>
          ⟨fun h p hp hpn => h p hpn hp, fun h p hpn hp => h p hp hpn⟩)
theorem rotate_back_mod (n r x : ℕ) (hn : 0 < n) : ((x + (n - r % n)) % n + r) % n = x % n := by
  have h1 : (x + (n - r % n)) % n + r ≡ x + (n - r % n) + r [MOD n] :=
    Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
  have h2 : x + (n - r % n) + r ≡ x + (n - r % n) + r % n [MOD n] :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _).symm
  have h3 : x + (n - r % n) + r % n = x + n := by have := Nat.mod_lt r hn; omega
  rw [h3] at h2
  exact h1.trans (h2.trans Nat.add_modEq_right)
theorem IsPrimitive.rotate {ρ : List α} (h : IsPrimitive ρ) (r : ℕ) : IsPrimitive (ρ.rotate r) := by
  rw [isPrimitive_iff_period] at h ⊢
  obtain ⟨hne, hper⟩ := h
  have hn : 0 < ρ.length := List.length_pos_iff.mpr hne
  refine ⟨by rw [Ne, List.rotate_eq_nil_iff]; exact hne, fun p hp hpn hdvd hrot => ?_⟩
  rw [List.length_rotate] at hpn hdvd
  apply hper p hp hpn hdvd
  rw [hasPeriod_iff_cyclic (by simpa using hn) (by simpa using hdvd)] at hrot
  rw [hasPeriod_iff_cyclic hn hdvd]
  intro i
  simp only [List.length_rotate] at hrot
  have := hrot (i + (ρ.length - r % ρ.length))
  rw [List.getElem?_rotate (Nat.mod_lt _ hn), List.getElem?_rotate (Nat.mod_lt _ hn),
    Nat.add_right_comm i _ p, rotate_back_mod _ _ _ hn, rotate_back_mod _ _ _ hn] at this
  exact this
def IsConjugate (ρ ρ' : List α) : Prop := ∃ r, ρ' = ρ.rotate r
theorem isConjugate_iff_isRotated {ρ ρ' : List α} : IsConjugate ρ ρ' ↔ ρ ~r ρ' :=
  ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩
instance sameClassDecidable [DecidableEq α] (ρ ρ' : List α) : Decidable (IsConjugate ρ ρ') :=
  decidable_of_iff _ isConjugate_iff_isRotated.symm
namespace IsConjugate
variable {ρ ρ' ρ'' : List α}
end IsConjugate
end DeciSigma1.Words


