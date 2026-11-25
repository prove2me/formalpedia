-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
-- name    : QuantumLTF_Membership_Supplement_symBand54
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T00:48:44.775055+00:00
-- url     : https://prove2.me/theorems/315c2dc4-562e-43a3-b6fb-43512c2ac300
-- title:
--   Blank-padded multinomial particle encoding for Theorem 5.4
-- statement:
--   Let $n, K, s \ge 1$ with $s = \lceil \log_2 n \rceil + 1$ (so $n \le 2^{s-1}$). We define the $s$-qubit blank-padded particle register encoding over the alphabet $\{0, \dots, n-1, \perp\}$:
--
--   1. **Blank symbol**: $|\perp\rangle$ is encoded by the $s$-bit MSB-first string `blankSym54 s` representing $2^{s-1}$ ($10\cdots 0$), whose most significant bit (bit $0$) is `true`.
--   2. **Particle alphabet**: `particleSym54 n s j` maps nonblank labels $j \in \{0, \dots, n-1\}$ to their MSB-first $s$-bit binary representations (with MSB `false`), and maps $j = n$ to $|\perp\rangle$. Because $n \le 2^{s-1}$, this map is injective on $\{0, \dots, n\}$ and its MSB equals `decide (j = n)`.
--   3. **Multinomial padded basis state**: For an occupation vector $\alpha : \mathrm{Fin}\, n \to \mathbb{N}$ satisfying $K \le |\alpha| = \sum_{i=0}^{n-1} \alpha_i \le 2K$, the state `multinomKet54 n s K \alpha` on $2K$ registers of $s$ qubits is the uniform superposition over all $2K$-tuples containing $\alpha_i$ copies of $|i\rangle$ for each $i < n$ and $2K - |\alpha|$ copies of $|\perp\rangle$, with amplitude
--
--   $$
--   \sqrt{\frac{\left(\prod_{i=0}^{n-1} \alpha_i!\right)(2K - |\alpha|)!}{(2K)!}}.
--   $$
--
--   We also provide wire-embedding (`embedPartAndDeg54`) and register-permutation (`permPartReg54`) helpers for embedding the $2Ks$ particle qubits into an arbitrary $(nq + e)$-qubit workspace alongside degree/ancilla wires.
--
--   **Formalization Note** Bit strings in `Qubits s` are indexed most significant bit first (`bitsToNat`), so wire `0` separates the blank symbol from all $n$ nonblank symbols without extra ancillas.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Section 5.3 (Theorem 5.4), pp. 66-69 (PDF pp. 67-70)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **Blank symbol `|⊥⟩` on `s` qubits** (`10⋯0`, i.e., `2^(s-1)` in MSB-first `natToBits s`).
For `s = Nat.clog 2 n + 1`, its MSB (bit `0`) is `true`, whereas every nonblank symbol
`natToBits s i` (`i < n ≤ 2^(s-1)`) has MSB `false`. -/
def blankSym54 (s : ℕ) : Qubits s :=
  natToBits s (2 ^ (s - 1))

/-- **Particle-alphabet encoding on `s` qubits** for `{0, ..., n - 1, ⊥}` indexed by
`Fin (n + 1)`: indices `j < n` map to `natToBits s j`, and `Fin.last n` maps to `blankSym54 s`. -/
def particleSym54 (n s : ℕ) (j : Fin (n + 1)) : Qubits s :=
  if j.val < n then natToBits s j.val else blankSym54 s

/-- **Ideal `2 * K`-particle padded multinomial basis ket** on `2 * K` registers of `s` qubits:
assigns amplitude `√((∏ i, α i !) * (2 * K - ∑ i, α i)! / (2 * K)!)` to every `2 * K`-register
string `y` containing `α i` copies of `natToBits s i` (`i : Fin n`) and `2 * K - ∑ i, α i`
copies of `blankSym54 s`, and `0` elsewhere. -/
noncomputable def multinomKet54 (n s K : ℕ) (α : Fin n → ℕ)
    (_hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K) : EuclideanSpace ℂ (Qubits (2 * K * s)) :=
  WithLp.toLp 2 fun y : Qubits (2 * K * s) =>
    if (∀ i : Fin n,
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) s y r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) =>
          splitReg (2 * K) s y r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i
    then
      ((Real.sqrt
        ((∏ i : Fin n, ((α i).factorial : ℝ)) *
          ((2 * K - ∑ i : Fin n, α i).factorial : ℝ) / ((2 * K).factorial : ℝ)) : ℝ) : ℂ)
    else 0

/-- Embeds an `N`-qubit state `ψ` onto wires `partEmb : Fin N ↪ Fin m`, tensored with the
computational-basis bitstring `degRest` on all wires outside `Set.range partEmb`. -/
noncomputable def embedPartAndDeg54 {m N : ℕ} (partEmb : Fin N ↪ Fin m)
    (ψ : EuclideanSpace ℂ (Qubits N)) (degRest : Qubits m) : EuclideanSpace ℂ (Qubits m) :=
  WithLp.toLp 2 fun z =>
    if ∀ a : Fin m, a ∉ Set.range partEmb → z a = degRest a then
      ψ (fun i => z (partEmb i))
    else 0

/-- Permutes the `2 * K` `s`-qubit particle registers embedded via `partEmb` so output register
`r` receives input register `σ r`, fixing all wires outside `Set.range partEmb`. -/
noncomputable def permPartReg54 {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) : Qubits m :=
  fun a =>
    if h : ∃ p : Fin (2 * K) × Fin s, partEmb (finProdFinEquiv p) = a then
      let p := Classical.choose h
      x (partEmb (finProdFinEquiv (σ p.1, p.2)))
    else x a

lemma particleSym54_lt {n s : ℕ} {j : Fin (n + 1)} (h : j.val < n) :
    particleSym54 n s j = natToBits s j.val :=
  if_pos h

lemma particleSym54_last (n s : ℕ) :
    particleSym54 n s (Fin.last n) = blankSym54 s := by
  simp [particleSym54]

private lemma bitsToNat_natToBits_54 {q k : ℕ} (hk : k < 2 ^ q) :
    bitsToNat (natToBits q k) = k := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hk]

lemma natToBits_msb_eq {s k : ℕ} (hs : 0 < s) (hk : k < 2 ^ s) :
    natToBits s k ⟨0, hs⟩ = decide (2 ^ (s - 1) ≤ k) := by
  cases s with
  | zero => exact absurd hs (Nat.lt_irrefl 0)
  | succ t =>
    have hsum : k =
        (if natToBits (t + 1) k 0 then 2 ^ t else 0) +
          ∑ j : Fin t, if natToBits (t + 1) k j.succ then 2 ^ (t - 1 - (j : ℕ)) else 0 := by
      conv_lhs => rw [← bitsToNat_natToBits_54 hk]
      unfold bitsToNat
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, tsub_zero, Fin.val_succ, Nat.succ_sub_one]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      have hexp : t - (j.val + 1) = t - 1 - j.val := by omega
      change (if natToBits (t + 1) k j.succ = true then 2 ^ (t - (j.val + 1)) else 0) =
        if natToBits (t + 1) k j.succ = true then 2 ^ (t - 1 - j.val) else 0
      rw [hexp]
    have htail :
        ∑ j : Fin t,
          (if natToBits (t + 1) k j.succ then 2 ^ (t - 1 - (j : ℕ)) else 0) < 2 ^ t := by
      calc
        ∑ j : Fin t, (if natToBits (t + 1) k j.succ then 2 ^ (t - 1 - (j : ℕ)) else 0)
            ≤ ∑ j : Fin t, 2 ^ (t - 1 - (j : ℕ)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs <;> simp
        _ = ∑ j : Fin t, 2 ^ (Fin.rev j).val := by
              refine Finset.sum_congr rfl fun j _ => ?_
              have : t - 1 - (j : ℕ) = (Fin.rev j).val := by rw [Fin.val_rev]; omega
              rw [this]
        _ = ∑ j : Fin t, 2 ^ j.val := Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
        _ = ∑ j ∈ Finset.range t, 2 ^ j := Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) t
        _ = 2 ^ t - 1 := by simpa using Nat.geomSum_eq (by norm_num : 2 ≤ 2) t
        _ < 2 ^ t := Nat.sub_lt (Nat.two_pow_pos t) Nat.zero_lt_one
    change natToBits (t + 1) k 0 = decide (2 ^ t ≤ k)
    cases hb : natToBits (t + 1) k 0 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, zero_add] at hsum
    · have hlt : k < 2 ^ t := by rw [hsum]; exact htail
      simp [Nat.not_le_of_lt hlt]
    · have hge : 2 ^ t ≤ k := by rw [hsum]; exact Nat.le_add_right _ _
      simp [hge]

lemma particleSym54_msb (n : ℕ) (j : Fin (n + 1)) :
    particleSym54 n (Nat.clog 2 n + 1) j ⟨0, Nat.succ_pos _⟩ = decide (j.val = n) := by
  have hle : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hpow : 2 ^ Nat.clog 2 n < 2 ^ (Nat.clog 2 n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  by_cases hj : j.val < n
  · rw [particleSym54_lt hj, natToBits_msb_eq (Nat.succ_pos _) (lt_of_lt_of_le hj (hle.trans hpow.le))]
    have h1 : ¬ (2 ^ Nat.clog 2 n ≤ j.val) := Nat.not_le_of_lt (lt_of_lt_of_le hj hle)
    have h2 : j.val ≠ n := Nat.ne_of_lt hj
    simp [h1, h2]
  · have hjn : j.val = n := by omega
    rw [particleSym54, if_neg hj, blankSym54]
    have hsub : Nat.clog 2 n + 1 - 1 = Nat.clog 2 n := Nat.add_sub_cancel _ 1
    rw [hsub, natToBits_msb_eq (Nat.succ_pos _) hpow]
    simp [hsub, hjn]

@[simp]
lemma embedPartAndDeg54_apply {m N : ℕ} (partEmb : Fin N ↪ Fin m)
    (ψ : EuclideanSpace ℂ (Qubits N)) (degRest : Qubits m) (z : Qubits m) :
    embedPartAndDeg54 partEmb ψ degRest z =
      if ∀ a : Fin m, a ∉ Set.range partEmb → z a = degRest a then
        ψ (fun i => z (partEmb i))
      else 0 := rfl

lemma particleSym54_inj (n : ℕ) :
    Function.Injective (particleSym54 n (Nat.clog 2 n + 1)) := by
  have hle : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hpow : 2 ^ Nat.clog 2 n < 2 ^ (Nat.clog 2 n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  intro i j hij
  have hmsb := congrFun hij ⟨0, Nat.succ_pos _⟩
  rw [particleSym54_msb n i, particleSym54_msb n j] at hmsb
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · rw [particleSym54_lt hi, particleSym54_lt hj] at hij
    have hnat := congrArg bitsToNat hij
    rw [bitsToNat_natToBits_54 (lt_of_lt_of_le hi (hle.trans hpow.le)),
        bitsToNat_natToBits_54 (lt_of_lt_of_le hj (hle.trans hpow.le))] at hnat
    exact Fin.ext hnat
  · have hjn : j.val = n := by omega
    have hine : i.val ≠ n := by omega
    simp [hine, hjn] at hmsb
  · have hin : i.val = n := by omega
    have hjne : j.val ≠ n := by omega
    simp [hin, hjne] at hmsb
  · ext; omega

@[simp]
lemma permPartReg54_part {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) (r : Fin (2 * K)) (b : Fin s) :
    permPartReg54 partEmb σ x (partEmb (finProdFinEquiv (r, b))) =
      x (partEmb (finProdFinEquiv (σ r, b))) := by
  unfold permPartReg54
  have hex : ∃ p : Fin (2 * K) × Fin s,
      partEmb (finProdFinEquiv p) = partEmb (finProdFinEquiv (r, b)) :=
    ⟨(r, b), rfl⟩
  rw [dif_pos hex]
  have hp : Classical.choose hex = (r, b) :=
    finProdFinEquiv.injective (partEmb.injective (Classical.choose_spec hex))
  rw [hp]

@[simp]
lemma permPartReg54_off {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) {a : Fin m} (ha : a ∉ Set.range partEmb) :
    permPartReg54 partEmb σ x a = x a := by
  unfold permPartReg54
  have hnex : ¬ ∃ p : Fin (2 * K) × Fin s, partEmb (finProdFinEquiv p) = a := by
    rintro ⟨p, rfl⟩
    exact ha ⟨finProdFinEquiv p, rfl⟩
  rw [dif_neg hnex]

@[simp]
lemma permPartReg54_one {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m) (x : Qubits m) :
    permPartReg54 partEmb 1 x = x := by
  funext a
  by_cases ha : a ∈ Set.range partEmb
  · obtain ⟨k, rfl⟩ := ha
    rcases finProdFinEquiv.surjective k with ⟨⟨r, b⟩, rfl⟩
    simp
  · exact permPartReg54_off partEmb 1 x ha

lemma permPartReg54_comp {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ₁ σ₂ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) :
    permPartReg54 partEmb σ₁ (permPartReg54 partEmb σ₂ x) =
      permPartReg54 partEmb (σ₂ * σ₁) x := by
  funext a
  by_cases ha : a ∈ Set.range partEmb
  · obtain ⟨k, rfl⟩ := ha
    rcases finProdFinEquiv.surjective k with ⟨⟨r, b⟩, rfl⟩
    simp [Equiv.Perm.mul_apply]
  · simp [permPartReg54_off partEmb _ _ ha]

lemma permPartReg54_symm_apply {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) :
    permPartReg54 partEmb σ.symm (permPartReg54 partEmb σ x) = x := by
  rw [permPartReg54_comp]
  change permPartReg54 partEmb (σ * σ⁻¹) x = x
  rw [mul_inv_cancel, permPartReg54_one]

lemma permPartReg54_apply_symm {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) :
    permPartReg54 partEmb σ (permPartReg54 partEmb σ.symm x) = x := by
  rw [permPartReg54_comp]
  change permPartReg54 partEmb (σ⁻¹ * σ) x = x
  rw [inv_mul_cancel, permPartReg54_one]

lemma permPartReg54_bijective {m K s : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) :
    Function.Bijective (permPartReg54 partEmb σ) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨permPartReg54 partEmb σ.symm, permPartReg54_symm_apply partEmb σ,
      permPartReg54_apply_symm partEmb σ⟩

end QuantumLTF.Membership.Supplement


