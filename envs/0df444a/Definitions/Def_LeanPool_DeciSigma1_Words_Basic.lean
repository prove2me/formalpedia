-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Words_Basic
-- name    : LeanPool_DeciSigma1_Words_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:39:15.602452+00:00
-- url     : https://prove2.me/theorems/9a96a169-acd7-4845-9967-15847a797981
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Words
open DeciSigma1.Words (pow)
section Streams
variable {α : Type*}
def streamPrefix (ξ : ℕ → α) (n : ℕ) : List α := List.ofFn (fun i : Fin n => ξ i)
@[simp] theorem length_streamPrefix (ξ : ℕ → α) (n : ℕ) :
    (streamPrefix ξ n).length = n := by simp [streamPrefix]
@[simp] theorem getElem_streamPrefix (ξ : ℕ → α) (n i : ℕ) (h : i < n) :
    (streamPrefix ξ n)[i]'(by simpa using h) = ξ i := by simp [streamPrefix]
@[simp] theorem take_streamPrefix (ξ : ℕ → α) (n k : ℕ) :
    (streamPrefix ξ n).take k = streamPrefix ξ (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [streamPrefix]
def prepend (w : List α) (ξ : ℕ → α) (i : ℕ) : α :=
  if h : i < w.length then w[i] else ξ (i - w.length)
def StreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop := ∀ i, ξ (i + p) = ξ i
theorem streamPeriod_mod {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    ξ n = ξ (n % p) := by
  by_cases hp : p = 0
  · simp [hp]
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < p
      · simp [Nat.mod_eq_of_lt hn]
      · have hle : p ≤ n := by omega
        calc
          ξ n = ξ (n - p) := by simpa [Nat.sub_add_cancel hle] using h (n - p)
          _ = ξ ((n - p) % p) := ih _ (by omega)
          _ = ξ (n % p) := by rw [← Nat.mod_eq_sub_mod hle]
theorem streamPeriod_prefix {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (n : ℕ) :
    List.HasPeriod (streamPrefix ξ n) p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hi' : i <
      n := by simpa only [length_streamPrefix] using (by omega : i < (streamPrefix ξ n).length)
  have hip : i + p < n := by simp only [length_streamPrefix] at hi; omega
  simp only [streamPrefix, List.getElem?_ofFn, dif_pos hi', dif_pos hip, h i]
theorem streamPeriod_shift {ξ : ℕ → α} {p : ℕ} (h : StreamPeriod ξ p) (k : ℕ) :
    StreamPeriod (fun i => ξ (k + i)) p := by
  intro i; simpa [Nat.add_assoc] using h (k + i)
def LeastStreamPeriod (ξ : ℕ → α) (p : ℕ) : Prop :=
  0 < p ∧ StreamPeriod ξ p ∧ ∀ q, 0 < q → StreamPeriod ξ q → p ≤ q
theorem period_of_suffix {ξ : ℕ → α} {p q k : ℕ} (hp : 0 < p)
    (hξ : StreamPeriod ξ p) (hq : StreamPeriod (fun i => ξ (k + i)) q) :
    StreamPeriod ξ q := by
  intro i
  have hlarge : k ≤ i + k * p := by nlinarith
  have hh := hq (i + k * p - k)
  change ξ (k + (i + k * p - k + q)) = ξ (k + (i + k * p - k)) at hh
  have he₁ : k + (i + k * p - k + q) = i + q + k * p := by omega
  have he₂ : k + (i + k * p - k) = i + k * p := by omega
  rw [he₁, he₂, streamPeriod_mod hξ (i + q + k * p),
    streamPeriod_mod hξ (i + k * p)] at hh
  simpa only [Nat.add_mul_mod_self_right, ← streamPeriod_mod hξ] using hh
theorem leastPeriod_suffix {ξ : ℕ → α} {p : ℕ} (hp : LeastStreamPeriod ξ p) (k : ℕ) :
    LeastStreamPeriod (fun i => ξ (k + i)) p := by
  refine ⟨hp.1, streamPeriod_shift hp.2.1 k, ?_⟩
  intro q hq hper
  exact hp.2.2 q hq (period_of_suffix hp.1 hp.2.1 hper)
end Streams
variable {α : Type}
def PeriodicFrom (ξ : ℕ → α) (A p : ℕ) : Prop := StreamPeriod (fun t => ξ (A + t)) p
theorem PeriodicFrom.mono {ξ : ℕ → α} {A A' p : ℕ} (h : PeriodicFrom ξ A p) (hA : A ≤ A') :
    PeriodicFrom ξ A' p := by
  intro t
  have := h (A' - A + t)
  simp only at this ⊢
  rwa [show A + (A' - A + t + p) = A' + (t + p) by omega,
    show A + (A' - A + t) = A' + t by omega] at this
theorem streamEq_of_agree {ξ η : ℕ → α} {p q : ℕ} (hξ : LeastStreamPeriod ξ p)
    (hη : LeastStreamPeriod η q) (h : ∀ t < p + q, ξ t = η t) : ∀ t, ξ t = η t := by
  set n := p + q
  have hw : streamPrefix ξ n = streamPrefix η n := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [streamPrefix, List.getElem_ofFn]
    exact h i (by simpa using hi)
  have hwp : (streamPrefix ξ n).HasPeriod p := streamPeriod_prefix hξ.2.1 n
  have hwq : (streamPrefix ξ n).HasPeriod q := hw ▸ streamPeriod_prefix hη.2.1 n
  have hg := hwp.gcd hwq (by simp only [length_streamPrefix, n]; omega)
  set g := Nat.gcd p q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left q hξ.1
  have hper : PeriodicOn (streamPrefix ξ n) g 0 n := by
    rw [periodicOn_iff_hasPeriod (Nat.zero_le _) (by simp)]
    simpa using hg
  -- positions below `n` congruent modulo `g` carry equal letters
  have hmod : ∀ x y, x < n → y < n → x % g = y % g → ξ x = ξ y := by
    intro x y hx hy hxy
    have := hper.eq_of_mod (Nat.zero_le x) (Nat.zero_le y) hx hy hxy
    rw [List.getElem?_eq_getElem (by simpa using hx), List.getElem?_eq_getElem (by simpa using hy),
      Option.some_inj] at this
    simpa [hx, hy] using this
  -- `g` is a period of `ξ`, hence `g = p`
  have hgp : g = p := by
    have hgξ : StreamPeriod ξ g := by
      intro i
      rw [streamPeriod_mod hξ.2.1 (i + g), streamPeriod_mod hξ.2.1 i]
      apply hmod _ _ (by have := Nat.mod_lt (i + g) hξ.1; omega)
        (by have := Nat.mod_lt i hξ.1; omega)
      rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left p q), Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left p q),
        Nat.add_mod_right]
    exact le_antisymm (Nat.le_of_dvd hξ.1 (Nat.gcd_dvd_left p q)) (hξ.2.2 g hgpos hgξ)
  -- likewise `g = q`
  have hmodη : ∀ x y, x < n → y < n → x % g = y % g → η x = η y := by
    intro x y hx hy hxy
    rw [← h x hx, ← h y hy]; exact hmod x y hx hy hxy
  have hgq : g = q := by
    have hgη : StreamPeriod η g := by
      intro i
      rw [streamPeriod_mod hη.2.1 (i + g), streamPeriod_mod hη.2.1 i]
      apply hmodη _ _ (by have := Nat.mod_lt (i + g) hη.1; omega)
        (by have := Nat.mod_lt i hη.1; omega)
      rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right p q),
        Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right p q), Nat.add_mod_right]
    exact le_antisymm (Nat.le_of_dvd hη.1 (Nat.gcd_dvd_right p q)) (hη.2.2 g hgpos hgη)
  intro t
  rw [streamPeriod_mod hξ.2.1 t, streamPeriod_mod hη.2.1 t, ← hgp, ← hgq]
  exact h _ (by have := Nat.mod_lt t hgpos; omega)
structure Ray (α : Type) where
  /-- The finite word before the periodic part. -/
  stem : List α
  /-- The repeated word. -/
  loop : List α
  loop_ne_nil : loop ≠ []
namespace Ray
variable (Ω : Ray α)
theorem loop_length_pos : 0 < Ω.loop.length := List.length_pos_iff.mpr Ω.loop_ne_nil
def periodicTail (n : ℕ) : α := Ω.loop[n % Ω.loop.length]'(Nat.mod_lt _ Ω.loop_length_pos)
def stream : ℕ → α := prepend Ω.stem Ω.periodicTail
variable {Ω}
theorem periodicTail_period_length : StreamPeriod Ω.periodicTail Ω.loop.length := by
  intro t; simp only [periodicTail, Nat.add_mod_right]
theorem stream_of_ge {n : ℕ} (h : Ω.stem.length ≤ n) :
    Ω.stream n = Ω.periodicTail (n - Ω.stem.length) := by
  simp only [stream, prepend, dif_neg (not_lt.mpr h)]
def OnsetAt (A : ℕ) : Prop :=
  ∀ t < Ω.stem.length - A, Ω.stream (A + t + Ω.loop.length) = Ω.stream (A + t)
instance [DecidableEq α] (A : ℕ) : Decidable (Ω.OnsetAt A) :=
  inferInstanceAs (Decidable (∀ t < _, _))
theorem onsetAt_iff {A : ℕ} : Ω.OnsetAt A ↔ PeriodicFrom Ω.stream A Ω.loop.length := by
  constructor
  · intro h t
    change Ω.stream (A + (t + Ω.loop.length)) = Ω.stream (A + t)
    by_cases ht : A + t < Ω.stem.length
    · rw [← Nat.add_assoc]; exact h t (by omega)
    · rw [stream_of_ge (by omega), stream_of_ge (by omega),
        show A + (t + Ω.loop.length) - Ω.stem.length = A + t - Ω.stem.length +
            Ω.loop.length by omega,
        periodicTail_period_length]
  · intro h t _
    have : Ω.stream (A + (t + Ω.loop.length)) = Ω.stream (A + t) := h t
    rwa [← Nat.add_assoc] at this
theorem exists_onsetAt (Ω : Ray α) : ∃ A, Ω.OnsetAt A := ⟨Ω.stem.length, fun t ht => by omega⟩
theorem exists_period (Ω : Ray α) :
    ∃ p, 0 < p ∧ ∀ t < Ω.loop.length, Ω.periodicTail (t + p) = Ω.periodicTail t :=
  ⟨Ω.loop.length, Ω.loop_length_pos, fun t _ => periodicTail_period_length t⟩
variable [DecidableEq α]
def onset (Ω : Ray α) : ℕ := Nat.find Ω.exists_onsetAt
def period (Ω : Ray α) : ℕ := Nat.find Ω.exists_period
theorem periodicFrom_onset : PeriodicFrom Ω.stream Ω.onset Ω.loop.length :=
  onsetAt_iff.mp (Nat.find_spec Ω.exists_onsetAt)
theorem periodicFrom_of_onset_le {A : ℕ} (h : Ω.onset ≤ A) :
    PeriodicFrom Ω.stream A Ω.loop.length :=
  periodicFrom_onset.mono h
theorem period_pos : 0 < Ω.period := (Nat.find_spec Ω.exists_period).1
theorem periodicTail_leastPeriod : StreamPeriod Ω.periodicTail Ω.period := by
  intro t
  have hs : ∀ t < Ω.loop.length, Ω.periodicTail (t + Ω.period) = Ω.periodicTail t :=
      (Nat.find_spec Ω.exists_period).2
  have hn := Ω.loop_length_pos
  calc Ω.periodicTail (t + Ω.period) = Ω.periodicTail ((t + Ω.period) % Ω.loop.length) :=
      streamPeriod_mod periodicTail_period_length _
    _ = Ω.periodicTail ((t % Ω.loop.length + Ω.period) % Ω.loop.length) := by rw [Nat.mod_add_mod]
    _ = Ω.periodicTail (t % Ω.loop.length + Ω.period) :=
        (streamPeriod_mod periodicTail_period_length _).symm
    _ = Ω.periodicTail (t % Ω.loop.length) := hs _ (Nat.mod_lt _ hn)
    _ = Ω.periodicTail t := (streamPeriod_mod periodicTail_period_length _).symm
theorem leastStreamPeriod_periodicTail : LeastStreamPeriod Ω.periodicTail Ω.period :=
  ⟨period_pos, periodicTail_leastPeriod, fun _ hq hqp => Nat.find_min' Ω.exists_period ⟨hq,
      fun t _ => hqp t⟩⟩
theorem leastStreamPeriod_shift {A : ℕ} (h : Ω.onset ≤ A) :
    LeastStreamPeriod (fun t => Ω.stream (A + t)) Ω.period := by
  set m := max A Ω.stem.length
  have hsuf : (fun i => (fun t => Ω.stream (A + t)) (m - A + i)) =
      fun i => Ω.periodicTail (m - Ω.stem.length + i) := by
    funext i
    simp only
    rw [stream_of_ge (by omega)]
    congr 1; omega
  have hleast : LeastStreamPeriod (fun i => (fun t => Ω.stream (A + t)) (m - A + i)) Ω.period := by
    rw [hsuf]; exact leastPeriod_suffix leastStreamPeriod_periodicTail _
  refine ⟨period_pos, ?_, fun q hq hqp => hleast.2.2 q hq (streamPeriod_shift hqp _)⟩
  exact period_of_suffix Ω.loop_length_pos (periodicFrom_of_onset_le h) hleast.2.1
theorem stream_suffix_eq_of_prefix_eq (Ω Ω' : Ray α) (a b : ℕ)
    (h : ∀ t < max (Ω.onset - a) (max (Ω'.onset - b) 0) + Ω.period + Ω'.period,
      Ω.stream (a + t) = Ω'.stream (b + t)) : ∀ t, Ω.stream (a + t) = Ω'.stream (b + t) := by
  set m := max (Ω.onset - a) (max (Ω'.onset - b) 0)
  have h1 := leastStreamPeriod_shift (Ω := Ω) (A := a + m) (by omega)
  have h2 := leastStreamPeriod_shift (Ω := Ω') (A := b + m) (by omega)
  have heq := streamEq_of_agree h1 h2 (fun t ht => by
    show Ω.stream (a + m + t) = Ω'.stream (b + m + t)
    rw [show a + m + t = a + (m + t) by ring, show b + m + t = b + (m + t) by ring]
    exact h _ (by omega))
  intro t
  by_cases ht : t < m
  · exact h t (by omega)
  · have : Ω.stream (a + m + (t - m)) = Ω'.stream (b + m + (t - m)) := heq (t - m)
    rwa [show a + m + (t - m) = a + t by omega, show b + m + (t - m) = b + t by omega] at this
instance decSuffixEq (Ω Ω' : Ray α) (a b : ℕ) :
    Decidable (∀ t, Ω.stream (a + t) = Ω'.stream (b + t)) :=
  decidable_of_iff (∀ t < max (Ω.onset - a) (max (Ω'.onset - b) 0) + Ω.period + Ω'.period,
      Ω.stream (a + t) = Ω'.stream (b + t))
    ⟨stream_suffix_eq_of_prefix_eq Ω Ω' a b, fun h t _ => h t⟩
def prefixBeforeOnset (Ω : Ray α) : List α := streamPrefix Ω.stream Ω.onset
def suffixBeforeOnset (Ω : Ray α) (J : ℕ) :
    List α := streamPrefix (fun t => Ω.stream (J + t)) (Ω.onset - J)
end Ray
end DeciSigma1.Words


