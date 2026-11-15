-- Prove2me | Definitions.Def_RPLib_S3_PCF
-- name    : RPLib_S3_PCF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:29:56.186337+00:00
-- url     : https://prove2.me/theorems/ef9560a0-575b-4702-a87b-4313e695ac7e
-- title:
--   Weight-two Ramanujan-Petersson library: counting the non-stable lines
-- statement:
--   Counting the non-stable lines.
--
--   For `γ` with `p ∣ det γ`, the number of lines `ℓ` of `F_p²` with `qv p γ ℓ ≠ 0` (the non-stable lines of `γ mod p`)
--   is `p - 1` if `p ∤ tr γ` (`card_qv_tr`), `p` if `p ∣ tr γ` and `p ∤ γ` (`card_qv_nil`), and `0` if `p ∣ γ`
--   (`card_qv_dvd`). Proved over any finite field for `qf a b c d` (`a d - b c = 0`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCE

/-!
# S3-DWS-Supersingular, part C (F): counting the non-stable lines

For `γ` with `p ∣ det γ`, the number of lines `ℓ` of `F_p²` with `qv p γ ℓ ≠ 0` (the non-stable lines of `γ mod p`)
is `p - 1` if `p ∤ tr γ` (`card_qv_tr`), `p` if `p ∣ tr γ` and `p ∤ γ` (`card_qv_nil`), and `0` if `p ∣ γ`
(`card_qv_dvd`). Proved over any finite field for `qf a b c d` (`a d - b c = 0`).
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

section Field

variable {K : Type*} [Field K] [Finite K] [DecidableEq K]

/-- The stable-line test of `!![a, b; c, d]` on the lines `none = [1 : 0]`-type and `some j` of `K²`. -/
def qf (a b c d : K) : Option K → K
  | none => b
  | some j => c + (d - a) * j - b * j ^ 2

lemma card_ne_add (f : Option K → K) (Z : Finset (Option K)) (hZ : ∀ ℓ, f ℓ = 0 ↔ ℓ ∈ Z) :
    Nat.card {ℓ // f ℓ ≠ 0} + Z.card = Nat.card K + 1 := by
  have h : Nat.card (Option K) = Nat.card {ℓ // f ℓ = 0} + Nat.card {ℓ // f ℓ ≠ 0} := card_split _
  have hz : Nat.card {ℓ // f ℓ = 0} = Z.card :=
    (Nat.card_congr (Equiv.subtypeEquivRight hZ)).trans (Nat.card_eq_finsetCard Z)
  rw [Finite.card_option] at h
  omega

lemma qf_key (a b c d j : K) (hdet : a * d - b * c = 0) :
    -b * (c + (d - a) * j - b * j ^ 2) = (b * j - d) * (b * j + a) := by
  linear_combination hdet

/-- Trace nonzero: two stable lines. -/
theorem card_qf_tr {a b c d : K} (hdet : a * d - b * c = 0) (htr : a + d ≠ 0) :
    Nat.card {ℓ // qf a b c d ℓ ≠ 0} = Nat.card K - 1 := by
  by_cases hb : b = 0
  · subst hb
    have had : a * d = 0 := by linear_combination hdet
    have hda : d - a ≠ 0 := by
      rcases mul_eq_zero.1 had with h | h
      · rw [h, sub_zero]; rwa [h, zero_add] at htr
      · intro h'; apply htr; linear_combination -h' + 2 * h
    have hZ : ∀ ℓ, qf a 0 c d ℓ = 0 ↔ ℓ ∈ ({none, some (-c / (d - a))} : Finset (Option K)) := by
      rintro (_ | j)
      · simp [qf]
      · simp only [qf, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, reduceCtorEq, false_or,
          zero_mul, sub_zero]
        rw [eq_div_iff hda]
        constructor <;> intro h <;> linear_combination h
    have h2 := card_ne_add _ _ hZ
    rw [Finset.card_pair (by simp)] at h2
    omega
  · have hne : d / b ≠ -a / b := by
      intro h; apply htr
      have := (div_left_inj' hb).1 h
      linear_combination this
    have hZ : ∀ ℓ, qf a b c d ℓ = 0 ↔ ℓ ∈ ({some (d / b), some (-a / b)} : Finset (Option K)) := by
      rintro (_ | j)
      · simp [qf, hb]
      · simp only [qf, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq]
        have e : c + (d - a) * j - b * j ^ 2 = 0 ↔ (b * j - d) * (b * j + a) = 0 := by
          rw [← qf_key a b c d j hdet, mul_eq_zero, or_iff_right (neg_ne_zero.2 hb)]
        rw [e, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, eq_div_iff hb, eq_div_iff hb, mul_comm j b]
    have h2 := card_ne_add _ _ hZ
    rw [Finset.card_pair (by simpa using hne)] at h2
    omega

/-- Trace zero, `A ≠ 0`: one stable line. -/
theorem card_qf_nil {a b c d : K} (hdet : a * d - b * c = 0) (htr : a + d = 0)
    (hA : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    Nat.card {ℓ // qf a b c d ℓ ≠ 0} = Nat.card K := by
  have hd : d = -a := by linear_combination htr
  subst hd
  by_cases hb : b = 0
  · subst hb
    have ha2 : a ^ 2 = 0 := by linear_combination -hdet
    have ha : a = 0 := (pow_eq_zero_iff two_ne_zero).1 ha2
    subst ha
    have hc : c ≠ 0 := fun hc => hA ⟨rfl, rfl, hc, by simp⟩
    have hZ : ∀ ℓ, qf 0 0 c (-0) ℓ = 0 ↔ ℓ ∈ ({none} : Finset (Option K)) := by
      rintro (_ | j)
      · simp [qf]
      · simp [qf, hc]
    have h2 := card_ne_add _ _ hZ
    rw [Finset.card_singleton] at h2
    omega
  · have hZ : ∀ ℓ, qf a b c (-a) ℓ = 0 ↔ ℓ ∈ ({some (-a / b)} : Finset (Option K)) := by
      rintro (_ | j)
      · simp [qf, hb]
      · simp only [qf, Finset.mem_singleton, Option.some.injEq]
        have e : c + (-a - a) * j - b * j ^ 2 = 0 ↔ (b * j - -a) * (b * j + a) = 0 := by
          rw [← qf_key a b c (-a) j hdet, mul_eq_zero, or_iff_right (neg_ne_zero.2 hb)]
        rw [e, sub_neg_eq_add, mul_self_eq_zero, add_eq_zero_iff_eq_neg, eq_div_iff hb, mul_comm j b]
    have h2 := card_ne_add _ _ hZ
    rw [Finset.card_singleton] at h2
    omega

theorem card_qf_zero : Nat.card {ℓ // qf (0 : K) 0 0 0 ℓ ≠ 0} = 0 := by
  have : IsEmpty {ℓ // qf (0 : K) 0 0 0 ℓ ≠ 0} := ⟨by rintro ⟨_ | j, h⟩ <;> simp [qf] at h⟩
  exact Nat.card_of_isEmpty

end Field

/-! ## The counts for `qv` -/

section Qv

variable {p : ℕ} [Fact p.Prime]

lemma qv_eq_qf (γ : Mat) (ℓ : Option (ZMod p)) :
    qv p γ ℓ = qf ((γ 0 0 : ℤ) : ZMod p) ((γ 0 1 : ℤ) : ZMod p) ((γ 1 0 : ℤ) : ZMod p) ((γ 1 1 : ℤ) : ZMod p) ℓ := by
  cases ℓ <;> rfl

lemma detCast_eq_zero_F {γ : Mat} (hn : (p : ℤ) ∣ γ.det) :
    ((γ 0 0 : ℤ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p) - ((γ 0 1 : ℤ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p) = 0 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hn
  rw [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_mul] at h
  exact h

lemma trace_cast_iff {γ : Mat} :
    ((γ 0 0 : ℤ) : ZMod p) + ((γ 1 1 : ℤ) : ZMod p) = 0 ↔ (p : ℤ) ∣ γ.trace := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Matrix.trace_fin_two, Int.cast_add]

lemma dvdMat_cast_iff {γ : Mat} :
    DvdMat p γ ↔ (((γ 0 0 : ℤ) : ZMod p) = 0 ∧ ((γ 0 1 : ℤ) : ZMod p) = 0 ∧ ((γ 1 0 : ℤ) : ZMod p) = 0 ∧
      ((γ 1 1 : ℤ) : ZMod p) = 0) := by
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, DvdMat, Fin.forall_fin_two]
  tauto

theorem card_qv_tr {γ : Mat} (hn : (p : ℤ) ∣ γ.det) (ht : ¬ (p : ℤ) ∣ γ.trace) :
    Nat.card {ℓ : Option (ZMod p) // qv p γ ℓ ≠ 0} = p - 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp only [qv_eq_qf]
  rw [card_qf_tr (detCast_eq_zero_F hn) (mt trace_cast_iff.1 ht), Nat.card_zmod]

theorem card_qv_nil {γ : Mat} (hn : (p : ℤ) ∣ γ.det) (ht : (p : ℤ) ∣ γ.trace) (hγ : ¬ DvdMat p γ) :
    Nat.card {ℓ : Option (ZMod p) // qv p γ ℓ ≠ 0} = p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp only [qv_eq_qf]
  rw [card_qf_nil (detCast_eq_zero_F hn) (trace_cast_iff.2 ht) (mt dvdMat_cast_iff.2 hγ), Nat.card_zmod]

theorem card_qv_dvd {γ : Mat} (hγ : DvdMat p γ) :
    Nat.card {ℓ : Option (ZMod p) // qv p γ ℓ ≠ 0} = 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨h1, h2, h3, h4⟩ := dvdMat_cast_iff.1 hγ
  simp only [qv_eq_qf, h1, h2, h3, h4]
  exact card_qf_zero

end Qv

end RamanujanPetersson.S3.DWSS


