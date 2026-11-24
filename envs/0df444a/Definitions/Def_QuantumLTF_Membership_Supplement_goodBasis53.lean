-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_goodBasis53
-- name    : QuantumLTF_Membership_Supplement_goodBasis53
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T08:00:32.608232+00:00
-- url     : https://prove2.me/theorems/5fe02a34-2388-48c9-b76d-1ec1e30da475
-- title:
--   Good basis-state predicate and reversible band-circuit suite for Theorem 5.3
-- statement:
--   Foundational basis predicates, block-permutation maps, and reversible circuit-suite specification for Theorem 5.3 (high-degree projection of quantum linear threshold function states).
--
--   Let $n, q, K, D, a \in \mathbb{N}$ denote the input dimension $n$, the per-coordinate register bit-width $q$ (with $M = 2^q \ge D \ge 2K + 1$), the degree-band parameter $K$, and the number of internal ancilla qubits $a$. A computational basis state $z \in \{0,1\}^{nq + 1 + a}$ decomposes uniquely into a degree register $x \in \{0,1\}^{nq}$, a branch flag $y \in \{0,1\}$, and an ancilla register $s \in \{0,1\}^a$ via the bijection $(x, y, s) \mapsto z$, where $x$ stores $n$ $q$-bit MSB-first integers $\alpha_0, \dots, \alpha_{n-1} \in \{0, \dots, 2^q - 1\}$.
--
--   1. **Good-band basis predicate.** A basis state $z$ lies in the target degree band if and only if $y = 1$, $s = 0^a$, $\alpha_i < D$ for all $0 \le i < n$, and
--   $$
--   K \le \sum_{i=0}^{n-1} \alpha_i \le 2K.
--   $$
--   We provide the canonical equivalence characterizing such basis states as flattened MSB-first encodings of tuples $\alpha : \{0,\dots,n-1\} \to \{0,\dots,2K\}$ satisfying $K \le \sum_i \alpha_i \le 2K$.
--
--   2. **First-hit block swap.** Given $R$ register blocks $B = (B_0, \dots, B_{R-1})$ with $B_i \in \{0,1\}^{m_{\mathrm{reg}}}$ and a flag bitstring $f \in \{0,1\}^R$, let $j^*(f) = \min\{j < R : f_j = 1\}$ when $f \neq 0^R$. The block-routing involution swaps $B_0$ and $B_{j^*(f)}$ when $f \neq 0^R$ and acts as the identity when $f = 0^R$.
--
--   3. **Reversible band-circuit suite.** The circuit suite bundles elementary reversible circuits over the universal $1$- and $2$-qubit gate set together with clean ancilla restoration ($|0\rangle \mapsto |0\rangle$) and a uniform gate-count constant $C_{\mathrm{circ}} > 0$:
--      - a good-band marker XORing the good-band predicate into a target qubit using at most $C_{\mathrm{circ}}\bigl(n(q + \lceil \log_2(nD + 2) \rceil + 1) + a + 1\bigr)$ elementary gates;
--      - a good-band phase reflection applying phase $-1$ on good basis states within the same gate-count bound;
--      - a zero-state phase reflection on $\{0,1\}^{nq + 1 + a}$ using at most $C_{\mathrm{circ}}(nq + a + 1)$ elementary gates;
--      - a first-hit block-swap circuit using at most $C_{\mathrm{circ}} R (m_{\mathrm{reg}} + 1)$ elementary gates to realize the first-hit block permutation controlled read-only on $f$.
--
--   This definition provides the shared basis interface and reversible circuit bundle consumed by the modular sub-lemmas and the top-level proof of Theorem 5.3.
--
--   **Formalization Note.** In Lean 4 (`QuantumLTF.Membership.Supplement`), `basisX53`, `basisY53`, `basisS53`, and `packBasis53` witness the isomorphism between `Qubits (n * q + 1 + a)` and `(Qubits (n * q), Bool, Qubits a)`, `isGoodBasis53` defines the Boolean good-band predicate (bridged to `flatReg` and `natToBits` via `isGoodBasis53_iff`), `firstTrue53` and `swappedBlocks53` formalize the first-hit swap permutation, and `structure BandCircuits53` specifies the `Circuit gates12` suite (`goodMarkerCircuit`, `goodReflectCircuit`, `zeroReflectCircuit`, `firstHitSwapCircuit`) with clean ancilla counts.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §5.2, Theorem 5.3, pp. 63–65

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- Extract the `n * q` degree-register wires from a `(n * q + 1 + a)`-qubit basis string. -/
def basisX53 (n q a : ℕ) (z : Qubits (n * q + 1 + a)) : Qubits (n * q) :=
  fun k => z (Fin.castAdd a (Fin.castSucc k))

/-- Extract the label wire `Y` (wire `n * q`) from a `(n * q + 1 + a)`-qubit basis string. -/
def basisY53 (n q a : ℕ) (z : Qubits (n * q + 1 + a)) : Bool :=
  z (Fin.castAdd a (Fin.last (n * q)))

/-- Extract the `a` internal ancilla wires from a `(n * q + 1 + a)`-qubit basis string. -/
def basisS53 (n q a : ℕ) (z : Qubits (n * q + 1 + a)) : Qubits a :=
  fun j => z (Fin.natAdd (n * q + 1) j)

/-- Pack `(x, y, s)` into a `(n * q + 1 + a)`-qubit basis string matching `Fin.append (Fin.snoc x y) s`. -/
def packBasis53 (n q a : ℕ) (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    Qubits (n * q + 1 + a) :=
  Fin.append (Fin.snoc (α := fun _ => Bool) x y) s

lemma basisX53_packBasis53 (n q a : ℕ) (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    basisX53 n q a (packBasis53 n q a x y s) = x := by
  funext k
  simp [basisX53, packBasis53, Fin.append_left, Fin.snoc_castSucc]

lemma basisY53_packBasis53 (n q a : ℕ) (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    basisY53 n q a (packBasis53 n q a x y s) = y := by
  simp [basisY53, packBasis53, Fin.append_left, Fin.snoc_last]

lemma basisS53_packBasis53 (n q a : ℕ) (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    basisS53 n q a (packBasis53 n q a x y s) = s := by
  funext j
  simp [basisS53, packBasis53, Fin.append_right]

lemma packBasis53_eta (n q a : ℕ) (z : Qubits (n * q + 1 + a)) :
    packBasis53 n q a (basisX53 n q a z) (basisY53 n q a z) (basisS53 n q a z) = z := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [packBasis53, Fin.append_left]
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp [basisY53]
    · simp [basisX53]
  · simp [packBasis53, basisS53, Fin.append_right]

/-- MSB-first natural number encoded in degree sub-register `i : Fin n` of `z`. -/
def basisDeg53 (n q a : ℕ) (z : Qubits (n * q + 1 + a)) (i : Fin n) : ℕ :=
  bitsToNat (splitReg n q (basisX53 n q a z) i)

/-- Good basis-state predicate for Theorem 5.3: `Y = true`, all `a` ancillas are `false`,
every sub-register `i < n` has degree `< D`, and the total degree lies in `[K, 2K]`. -/
def isGoodBasis53 (n q K D a : ℕ) (z : Qubits (n * q + 1 + a)) : Bool :=
  let degSum := ∑ i : Fin n, basisDeg53 n q a z i
  decide (basisY53 n q a z = true ∧
    (∀ j : Fin a, basisS53 n q a z j = false) ∧
    (∀ i : Fin n, basisDeg53 n q a z i < D) ∧
    K ≤ degSum ∧ degSum ≤ 2 * K)

lemma bitsToNat_natToBits {q k : ℕ} (hk : k < 2 ^ q) :
    bitsToNat (natToBits q k) = k := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hk]

lemma natToBits_bitsToNat {q : ℕ} (b : Qubits q) :
    natToBits q (bitsToNat b) = b := by
  have hlt : bitsToNat b < 2 ^ q := by
    rw [← bitsEquivFin_apply]
    exact (bitsEquivFin q b).isLt
  apply (bitsEquivFin q).injective
  ext
  rw [bitsEquivFin_apply, bitsToNat_natToBits hlt]
  exact (bitsEquivFin_apply b).symm

lemma flatReg_splitReg (n b : ℕ) (x : Qubits (n * b)) :
    flatReg n b (splitReg n b x) = x := by
  funext k
  change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
  rw [finProdFinEquiv.apply_symm_apply]

lemma splitReg_flatReg (n b : ℕ) (f : Fin n → Qubits b) :
    splitReg n b (flatReg n b f) = f := by
  funext i j
  change f (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = f i j
  rw [finProdFinEquiv.symm_apply_apply]

lemma flatReg_inj (n b : ℕ) : Function.Injective (flatReg n b) := by
  intro f g h
  have := congrArg (splitReg n b) h
  simpa [splitReg_flatReg] using this

lemma flatReg_natToBits_inj {n q D : ℕ} (hDq : D ≤ 2 ^ q) :
    Function.Injective (fun α : Fin n → Fin D => flatReg n q (fun i => natToBits q (α i))) := by
  intro α β h
  have h1 : (fun i => natToBits q (α i)) = (fun i => natToBits q (β i)) := flatReg_inj n q h
  funext i
  have hi := congrArg bitsToNat (congrFun h1 i)
  rw [bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt hDq),
      bitsToNat_natToBits (lt_of_lt_of_le (β i).isLt hDq)] at hi
  exact Fin.ext hi

lemma isGoodBasis53_iff {n q K D a : ℕ} (hKD : 2 * K + 1 ≤ D) (hDq : D ≤ 2 ^ q)
    (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    isGoodBasis53 n q K D a (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) = true ↔
      y = true ∧ s = (fun _ => false) ∧
      ∃ α : Fin n → Fin (2 * K + 1),
        x = flatReg n q (fun i => natToBits q (α i)) ∧
        K ≤ ∑ i : Fin n, (α i : ℕ) ∧ ∑ i : Fin n, (α i : ℕ) ≤ 2 * K := by
  change isGoodBasis53 n q K D a (packBasis53 n q a x y s) = true ↔ _
  simp only [isGoodBasis53, basisDeg53, basisX53_packBasis53, basisY53_packBasis53,
    basisS53_packBasis53, decide_eq_true_eq]
  constructor
  · rintro ⟨hy, hs, _, hK_lo, hK_hi⟩
    refine ⟨hy, funext hs, ?_⟩
    have hle2K : ∀ i : Fin n, bitsToNat (splitReg n q x i) ≤ 2 * K := fun i =>
      le_trans (Finset.single_le_sum (fun (j : Fin n) _ => Nat.zero_le (bitsToNat (splitReg n q x j)))
        (Finset.mem_univ i)) hK_hi
    let α : Fin n → Fin (2 * K + 1) := fun i =>
      ⟨bitsToNat (splitReg n q x i), Nat.lt_succ_of_le (hle2K i)⟩
    refine ⟨α, ?_, hK_lo, hK_hi⟩
    conv_lhs => rw [← flatReg_splitReg n q x]
    congr 1
    funext i
    exact (natToBits_bitsToNat (splitReg n q x i)).symm
  · rintro ⟨hy, hs, α, hx, hK_lo, hK_hi⟩
    refine ⟨hy, fun j => congrFun hs j, ?_, ?_⟩
    · intro i
      rw [hx, splitReg_flatReg, bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt (le_trans hKD hDq))]
      exact lt_of_lt_of_le (α i).isLt hKD
    · have hsum : (∑ i : Fin n, bitsToNat (splitReg n q x i)) = ∑ i : Fin n, (α i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hx, splitReg_flatReg, bitsToNat_natToBits (lt_of_lt_of_le (α i).isLt (le_trans hKD hDq))]
      rw [hsum]
      exact ⟨hK_lo, hK_hi⟩

/-- Index of the first `true` coordinate in `f : Qubits R`, or `R` if none exists. -/
def firstTrue53Aux : (R : ℕ) → Qubits R → ℕ
  | 0, _ => 0
  | R + 1, f => if f 0 then 0 else 1 + firstTrue53Aux R (fun i => f i.succ)

lemma firstTrue53Aux_lt {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) :
    firstTrue53Aux R f < R := by
  induction R with
  | zero => rcases hf with ⟨j, _⟩; exact Fin.elim0 j
  | succ R ih =>
    dsimp only [firstTrue53Aux]
    by_cases h0 : f 0 = true
    · rw [if_pos h0]; exact Nat.zero_lt_succ R
    · rw [if_neg h0]
      rcases hf with ⟨j, hj⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact False.elim (h0 hj)
      · have hlt := Nat.succ_lt_succ (ih (fun i => f i.succ) ⟨j', hj⟩)
        change firstTrue53Aux R (fun i => f i.succ) + 1 < R + 1 at hlt
        omega

/-- Least index `j : Fin R` where `f j = true`, given `∃ j, f j = true`. -/
def firstTrue53 {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) : Fin R :=
  ⟨firstTrue53Aux R f, firstTrue53Aux_lt f hf⟩

lemma firstTrue53_spec {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) :
    f (firstTrue53 f hf) = true ∧ ∀ k : Fin R, k < firstTrue53 f hf → f k = false := by
  induction R with
  | zero => rcases hf with ⟨j, _⟩; exact Fin.elim0 j
  | succ R ih =>
    by_cases h0 : f 0 = true
    · have hidx : firstTrue53 f hf = 0 := by
        apply Fin.ext
        simp [firstTrue53, firstTrue53Aux, h0]
      rw [hidx]
      exact ⟨h0, fun k hk => False.elim (Nat.not_lt_zero k.1 hk)⟩
    · have hf' : ∃ j : Fin R, f j.succ = true := by
        rcases hf with ⟨j, hj⟩
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact False.elim (h0 hj)
        · exact ⟨j', hj⟩
      have hsucc : firstTrue53 f hf = (firstTrue53 (fun i => f i.succ) hf').succ := by
        apply Fin.ext
        simp [firstTrue53, firstTrue53Aux, h0, Nat.add_comm]
      have hrec := ih (fun i => f i.succ) hf'
      rw [hsucc]
      refine ⟨hrec.1, fun k hk => ?_⟩
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · exact Bool.eq_false_iff.mpr h0
      · exact hrec.2 k' (Fin.succ_lt_succ_iff.mp hk)

lemma firstTrue53Aux_eq_iff {R : ℕ} (f : Qubits R) (j : Fin R) :
    j.1 = firstTrue53Aux R f ↔ f j = true ∧ ∀ k : Fin R, k.1 < j.1 → f k = false := by
  constructor
  · intro hj
    have hf : ∃ i : Fin R, f i = true := by
      induction R with
      | zero => exact Fin.elim0 j
      | succ R ih =>
        dsimp only [firstTrue53Aux] at hj
        by_cases h0 : f 0 = true
        · exact ⟨0, h0⟩
        · rw [if_neg h0] at hj
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · exfalso
            simp only [Fin.val_zero] at hj
            omega
          · have hj' : j'.1 = firstTrue53Aux R (fun i => f i.succ) := by
              simp only [Fin.val_succ] at hj
              omega
            obtain ⟨i, hi⟩ := ih (fun i => f i.succ) j' hj'
            exact ⟨i.succ, hi⟩
    have hsp := firstTrue53_spec f hf
    have hj_eq : j = firstTrue53 f hf := Fin.ext hj
    rw [hj_eq]
    exact ⟨hsp.1, fun k hk => hsp.2 k hk⟩
  · rintro ⟨hj, hprev⟩
    have hf : ∃ i : Fin R, f i = true := ⟨j, hj⟩
    have hsp := firstTrue53_spec f hf
    apply Nat.le_antisymm
    · by_contra hgt
      have hlt : firstTrue53 f hf < j := Nat.lt_of_not_ge hgt
      have hf_f := hprev (firstTrue53 f hf) hlt
      rw [hsp.1] at hf_f
      exact absurd hf_f (by decide)
    · by_contra hgt
      have hlt : j < firstTrue53 f hf := Nat.lt_of_not_ge hgt
      have hf_f := hsp.2 j hlt
      rw [hj] at hf_f
      exact absurd hf_f (by decide)

lemma firstTrue53Aux_eq_self_of_all_false {R : ℕ} (f : Qubits R)
    (hf : ∀ j : Fin R, f j = false) : firstTrue53Aux R f = R := by
  induction R with
  | zero => rfl
  | succ R ih =>
    simp [firstTrue53Aux, hf 0, ih (fun i => f i.succ) (fun i => hf i.succ), Nat.add_comm]

/-- Permute `R` register blocks by swapping slot `0` with `firstTrue53 f` when `∃ j, f j = true`. -/
def swappedBlocks53 {R m_reg : ℕ} (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    Fin R → Qubits m_reg :=
  if h : ∃ j : Fin R, f j = true then
    fun i => blocks (Equiv.swap (⟨0, (firstTrue53 f h).pos⟩ : Fin R) (firstTrue53 f h) i)
  else
    blocks

lemma swappedBlocks53_eq_swap {R m_reg : ℕ} (blocks : Fin R → Qubits m_reg) (f : Qubits R)
    (h : ∃ j : Fin R, f j = true) :
    swappedBlocks53 blocks f =
      fun i => blocks (Equiv.swap (⟨0, (firstTrue53 f h).pos⟩ : Fin R) (firstTrue53 f h) i) :=
  dif_pos h

lemma swappedBlocks53_of_all_false {R m_reg : ℕ} (blocks : Fin R → Qubits m_reg) (f : Qubits R)
    (h : ∀ j : Fin R, f j = false) :
    swappedBlocks53 blocks f = blocks := by
  rw [swappedBlocks53, dif_neg]
  rintro ⟨j, hj⟩
  rw [h j] at hj
  exact Bool.false_ne_true hj

lemma swappedBlocks53_zero {R m_reg : ℕ} (blocks : Fin R → Qubits m_reg) (f : Qubits R)
    (h : ∃ j : Fin R, f j = true) :
    swappedBlocks53 blocks f ⟨0, (firstTrue53 f h).pos⟩ = blocks (firstTrue53 f h) := by
  simp [swappedBlocks53_eq_swap blocks f h]

lemma swappedBlocks53_zero' {R m_reg : ℕ} [NeZero R] (blocks : Fin R → Qubits m_reg) (f : Qubits R)
    (h : ∃ j : Fin R, f j = true) :
    swappedBlocks53 blocks f 0 = blocks (firstTrue53 f h) :=
  swappedBlocks53_zero blocks f h

lemma swappedBlocks53_invol {R m_reg : ℕ} (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    swappedBlocks53 (swappedBlocks53 blocks f) f = blocks := by
  by_cases h : ∃ j : Fin R, f j = true
  · simp [swappedBlocks53_eq_swap _ f h]
  · simp [swappedBlocks53, dif_neg h]

lemma swappedBlocks53_inj {R m_reg : ℕ} (f : Qubits R) :
    Function.Injective (fun blocks : Fin R → Qubits m_reg => swappedBlocks53 blocks f) := by
  intro a b hab
  have := congrArg (fun x => swappedBlocks53 x f) hab
  simpa [swappedBlocks53_invol] using this

/-- Circuit suite over `gates12` implementing the Theorem 5.3 degree-band marker, reflections,
and first-hit block swap with clean ancillas restored to `|0⟩`. -/
structure BandCircuits53 where
  C_circ : ℝ
  hC_circ_pos : 0 < C_circ
  ancMarker : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  goodMarkerCircuit : (n K D q a : ℕ) →
    Circuit gates12 ((n * q + 1 + a) + 1 + ancMarker n K D q a)
  goodMarker_size : ∀ (n K D q a : ℕ),
    ((goodMarkerCircuit n K D q a).length : ℝ) ≤
      C_circ * (n * (q + Nat.clog 2 (n * D + 2) + 1) + a + 1)
  goodMarker_act : ∀ (n K D q a : ℕ) (z : Qubits (n * q + 1 + a)) (b : Bool),
    act (goodMarkerCircuit n K D q a).unitary
        (ket (Fin.append (Fin.snoc (α := fun _ => Bool) z b)
          (fun _ : Fin (ancMarker n K D q a) => false))) =
      ket (Fin.append (Fin.snoc (α := fun _ => Bool) z (xor b (isGoodBasis53 n q K D a z)))
        (fun _ : Fin (ancMarker n K D q a) => false))
  ancGoodRefl : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  goodReflectCircuit : (n K D q a : ℕ) →
    Circuit gates12 ((n * q + 1 + a) + ancGoodRefl n K D q a)
  goodReflect_size : ∀ (n K D q a : ℕ),
    ((goodReflectCircuit n K D q a).length : ℝ) ≤
      C_circ * (n * (q + Nat.clog 2 (n * D + 2) + 1) + a + 1)
  goodReflect_act : ∀ (n K D q a : ℕ) (z : Qubits (n * q + 1 + a)),
    act (goodReflectCircuit n K D q a).unitary
        (ket (Fin.append z (fun _ : Fin (ancGoodRefl n K D q a) => false))) =
      (if isGoodBasis53 n q K D a z then (-1 : ℂ) else 1) •
        ket (Fin.append z (fun _ : Fin (ancGoodRefl n K D q a) => false))
  ancZeroRefl : ℕ → ℕ → ℕ → ℕ
  zeroReflectCircuit : (n q a : ℕ) →
    Circuit gates12 ((n * q + 1 + a) + ancZeroRefl n q a)
  zeroReflect_size : ∀ (n q a : ℕ),
    ((zeroReflectCircuit n q a).length : ℝ) ≤ C_circ * (n * q + a + 1)
  zeroReflect_act : ∀ (n q a : ℕ) (z : Qubits (n * q + 1 + a)),
    act (zeroReflectCircuit n q a).unitary
        (ket (Fin.append z (fun _ : Fin (ancZeroRefl n q a) => false))) =
      (if z = (fun _ => false) then (-1 : ℂ) else 1) •
        ket (Fin.append z (fun _ : Fin (ancZeroRefl n q a) => false))
  ancFirstHitSwap : ℕ → ℕ → ℕ
  firstHitSwapCircuit : (R m_reg : ℕ) →
    Circuit gates12 ((R * m_reg) + R + ancFirstHitSwap R m_reg)
  firstHitSwap_size : ∀ (R m_reg : ℕ),
    ((firstHitSwapCircuit R m_reg).length : ℝ) ≤ C_circ * R * (m_reg + 1)
  firstHitSwap_act : ∀ (R m_reg : ℕ) (blocks : Fin R → Qubits m_reg) (f : Qubits R),
    act (firstHitSwapCircuit R m_reg).unitary
        (ket (Fin.append (Fin.append (flatReg R m_reg blocks) f)
          (fun _ : Fin (ancFirstHitSwap R m_reg) => false))) =
      ket (Fin.append (Fin.append (flatReg R m_reg (swappedBlocks53 blocks f)) f)
        (fun _ : Fin (ancFirstHitSwap R m_reg) => false))

end QuantumLTF.Membership.Supplement


