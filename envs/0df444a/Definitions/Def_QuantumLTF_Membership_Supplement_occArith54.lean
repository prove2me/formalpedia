-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_occArith54
-- name    : QuantumLTF_Membership_Supplement_occArith54
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T02:28:28.912095+00:00
-- url     : https://prove2.me/theorems/3e6147f3-6d6f-5ede-bcfd-b2b87ad83fa4
-- title:
--   Section V occupation-to-NSIL combinatorics and reversible gates12 arithmetic primitives (OccArith54)
-- statement:
--   Defines the pure second-to-first-quantization combinatorics (`prefSum54`, `exclPrefSum54`, `modeOf54`, `Sec5Rec54`, `keyW2_54`, `keyW3_54`, `keyW8_54`, `keyW8_0_54`, and the record lists `wtilde2_54`, `wtilde3_54`, `wtilde6_54`, `wtilde8_54`, `wtildef_54`), classical bit-register permutation functions (`copyRegFn54`, `setConstFn54`, `eqConstFn54`, `addInPlaceFn54`, `subInPlaceFn54`, `ctrlCopyRegFn54`), and the bundled `OccArith54` circuit-suite structure over `gates12` (`LayeredCircuit`).
--
--   1. **Section V Record Combinatorics:** For an occupation vector $\alpha : \mathrm{Fin}\,m \to \mathbb{N}$ with $\sum_{j=0}^{m-1} \alpha_j = N$, `prefSum54` gives $p_i = \sum_{j \le i} \alpha_j$ and `modeOf54` maps each particle rank $c < N$ to the unique mode $i < m$ with $\sum_{j < i} \alpha_j \le c < \sum_{j \le i} \alpha_j$. The lists `wtilde2_54`..`wtildef_54` encode the interleaved mode-and-particle tuples $(a, b, c) \in \mathbb{N}^3$ under the lexicographic orders `keyW2_54`, `keyW3_54`, `keyW8_54`, and `keyW8_0_54`.
--
--   2. **Reversible Arithmetic and Encoding Primitives (`OccArith54`):** Bundles exact `ImplementsOnClean` / unitary specifications and linear gate counts over `gates12` for bitwise register copy (`copyRegCircuit`, size $w$), constant XOR (`setConstCircuit`, size $\le w$), constant equality comparison (`eqConstCircuit`, size $\le 14w + 12$), LSB-first Cuccaro ripple-carry addition and subtraction (`addInPlaceCircuit` and `subInPlaceCircuit`, size $14w$), controlled bitwise copy (`ctrlCopyRegCircuit`, size $5w$), and in-place MSB-first particle-symbol encoding `encodeParticleSym54Circuit` (size $\le 13s$) mapping $|\mathrm{bin}_s(j), 0^{s-1}\rangle \mapsto |\mathrm{particleSym54}(n, s, j), 0^{s-1}\rangle$, together with the Section V sorted-prefix characterizations `wtilde2_sort_prefix` and `wtildef_sort_prefix`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section V); Cuccaro et al. (2004), A new quantum ripple-carry addition circuit; Krivcenko, Nguyen, de Wolf [KNW26], Fast Quantum Algorithms for Learning Linear Threshold Functions (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54

set_option autoImplicit false

/-!
# `[LCG26, Section V]` Combinatorics and Reversible Arithmetic Primitives (Definitions)

Defines the pure second-to-first-quantization combinatorics (`prefSum54`, `exclPrefSum54`,
`modeOf54`, `Sec5Rec54`, `wtilde2_54`..`wtildef_54`), classical bit-register specifications, and the
`OccArith54` `gates12` circuit-suite interface for `QuantumLTF.Membership.Supplement.occupation_to_nsil_54`.
-/

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! ### `[LCG26, Section V]` Prefix Sums, Mode Map & Record Lists -/

/-- Inclusive prefix sum `p_i = ∑_{j ≤ i} α j`. -/
def prefSum54 {m : ℕ} (α : Fin m → ℕ) (i : Fin m) : ℕ :=
  ∑ j : Fin m, if j ≤ i then α j else 0

/-- Exclusive prefix sum `∑_{j < i} α j`. -/
def exclPrefSum54 {m : ℕ} (α : Fin m → ℕ) (i : Fin m) : ℕ :=
  ∑ j : Fin m, if j < i then α j else 0

/-- Mode index `i < m` of the `c`-th particle (`c < ∑ j, α j`). -/
def modeOf54 {m : ℕ} (α : Fin m → ℕ) (c : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin m => prefSum54 α r ≤ c).card

/-- Record `(a, b, c) : ℕ × ℕ × ℕ` representing mode/marker `a`, payload `b`, prefix/index `c`. -/
abbrev Sec5Rec54 := ℕ × ℕ × ℕ

/-- `Γ_{W_2}` key: lexicographic `(a, c)`. -/
def keyW2_54 (t : Sec5Rec54) : ℕ ×ₗ ℕ := toLex (t.1, t.2.2)

/-- `Γ_{W_3}` key: lexicographic `(c, a)`. -/
def keyW3_54 (t : Sec5Rec54) : ℕ ×ₗ ℕ := toLex (t.2.2, t.1)

/-- `Γ_{W_8}` key: lexicographic `(b, if a < m then 1 else 0, c)`. -/
def keyW8_54 (m : ℕ) (t : Sec5Rec54) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (t.2.1, toLex (if t.1 < m then 1 else 0, t.2.2))

/-- Modified `Γ_{W_8}` key ignoring `c` on mode records (`a < m`), used for trace-reversible unrouting. -/
def keyW8_0_54 (m : ℕ) (t : Sec5Rec54) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (t.2.1, toLex (if t.1 < m then 1 else 0, if t.1 < m then 0 else t.2.2))

/-- Initial tuple list `Wtilde_2` of length `m + N`. -/
def wtilde2_54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : List Sec5Rec54 :=
  (List.finRange m).map (fun i => (i.1, 0, prefSum54 α i)) ++
    (List.finRange N).map (fun j => (m, 0, j.1))

/-- Number of elements of `wtilde2_54` strictly preceding `t` under `keyW3_54 = (c, a)`. -/
def wtilde3Rank54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) (t : Sec5Rec54) : ℕ :=
  ((wtilde2_54 α N).filter (fun u => decide (keyW3_54 u < keyW3_54 t))).length

/-- Sorted tuple list `Wtilde_3` obtained by sorting `wtilde2_54` under `keyW3_54`. -/
def wtilde3_54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : List Sec5Rec54 :=
  (wtilde2_54 α N).mergeSort (fun x y => decide (keyW3_54 x ≤ keyW3_54 y))

/-- Tuple list `Wtilde_6` with modes `(i, i, p_i)` and particles `(m, modeOf54 α j, j)`. -/
def wtilde6_54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : List Sec5Rec54 :=
  (List.finRange m).map (fun i => (i.1, i.1, prefSum54 α i)) ++
    (List.finRange N).map (fun j => (m, modeOf54 α j.1, j.1))

/-- Clear the third coordinate `c` on mode records (`a < m`). -/
def wtilde8Transform54 (m : ℕ) (t : Sec5Rec54) : Sec5Rec54 :=
  if t.1 < m then (t.1, t.1, 0) else t

/-- Tuple list `Wtilde_8` sorted under `keyW8_54 m`. -/
def wtilde8_54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : List Sec5Rec54 :=
  ((wtilde6_54 α N).mergeSort (fun x y => decide (keyW3_54 x ≤ keyW3_54 y))).map
    (wtilde8Transform54 m)

/-- Final sorted NSIL-augmented tuple list `Wtilde_f`. -/
def wtildef_54 {m : ℕ} (α : Fin m → ℕ) (N : ℕ) : List Sec5Rec54 :=
  (List.finRange m).map (fun i => (i.1, i.1, 0)) ++
    (List.finRange N).map (fun j => (m, modeOf54 α j.1, j.1))

/-! ### Classical Arithmetic & Wire-Embedding Helpers -/

/-- Disjoint union of two wire embeddings `Fin a ↪ Fin m` and `Fin b ↪ Fin m`. -/
def combineEmb54 {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) : Fin (a + b) ↪ Fin m where
  toFun := Fin.addCases ea eb
  inj' x y h := by
    induction x using Fin.addCases with
    | left ix =>
      induction y using Fin.addCases with
      | left iy => simp only [Fin.addCases_left] at h; rw [ea.injective h]
      | right jy =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        exact absurd h (hdisj ix jy)
    | right jx =>
      induction y using Fin.addCases with
      | left iy =>
        simp only [Fin.addCases_right, Fin.addCases_left] at h
        exact absurd h.symm (hdisj iy jx)
      | right jy => simp only [Fin.addCases_right] at h; rw [eb.injective h]

@[simp] lemma combineEmb54_castAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (i : Fin a) :
    combineEmb54 ea eb hdisj (Fin.castAdd b i) = ea i := by
  change Fin.addCases ea eb (Fin.castAdd b i) = ea i; simp

@[simp] lemma combineEmb54_natAdd {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hdisj : ∀ i j, ea i ≠ eb j) (j : Fin b) :
    combineEmb54 ea eb hdisj (Fin.natAdd a j) = eb j := by
  change Fin.addCases ea eb (Fin.natAdd a j) = eb j; simp

/-- Bitwise XOR copy `(a, b) ↦ (a, b ^^^ a)` on two `w`-qubit registers. -/
def copyRegFn54 (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  fun u => if w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by have := u.isLt; omega⟩) else x u

/-- Classical constant XOR `x ↦ x ^^^ natToBitsLSB w c`. -/
def setConstFn54 (w c : ℕ) (x : Qubits w) : Qubits w :=
  fun i => xor (x i) (natToBitsLSB w c i)

/-- Classical constant equality toggle `(x, t) ↦ (x, t ^^^ decide (x = natToBitsLSB w c))`. -/
def eqConstFn54 (w c : ℕ) (x : Qubits (w + 1)) : Qubits (w + 1) :=
  Function.update x ⟨w, by omega⟩
    (xor (x ⟨w, by omega⟩)
      (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = natToBitsLSB w c i)))

/-- In-place LSB-first `w`-bit adder `(a, b) ↦ (a, (a + b) mod 2^w)`. -/
def addInPlaceFn54 (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let sum := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else sum ⟨i.1 - w, by omega⟩

/-- In-place LSB-first `w`-bit subtractor `(a, b) ↦ (a, (2^w + b - a) mod 2^w)`. -/
def subInPlaceFn54 (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let diff := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else diff ⟨i.1 - w, by omega⟩

/-- Controlled bitwise copy `(ctrl, a, b) ↦ (ctrl, a, if ctrl then b ^^^ a else b)`. -/
def ctrlCopyRegFn54 (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  fun u =>
    if x ⟨0, by omega⟩ then
      if 1 + w ≤ u.1 then xor (x u) (x ⟨u.1 - w, by omega⟩) else x u
    else x u

/-- Bundled Section V combinatorics and reversible `gates12` arithmetic / encoding primitives for
Stage A (`occupation_to_nsil_54`). -/
structure OccArith54 where
  prefSum_eq_excl_add : ∀ {m : ℕ} (α : Fin m → ℕ) (i : Fin m),
    prefSum54 α i = exclPrefSum54 α i + α i
  prefSum_mono : ∀ {m : ℕ} (α : Fin m → ℕ), Monotone (prefSum54 α)
  exclPrefSum_le_prefSum_of_lt : ∀ {m : ℕ} (α : Fin m → ℕ) {i j : Fin m}, i < j →
    prefSum54 α i ≤ exclPrefSum54 α j
  exclPrefSum_zero : ∀ {m : ℕ} (α : Fin (m + 1) → ℕ), exclPrefSum54 α 0 = 0
  prefSum_last : ∀ {m : ℕ} (α : Fin (m + 1) → ℕ),
    prefSum54 α (Fin.last m) = ∑ j : Fin (m + 1), α j
  prefSum_le_sum : ∀ {m : ℕ} (α : Fin m → ℕ) (i : Fin m),
    prefSum54 α i ≤ ∑ j : Fin m, α j
  modeOf_lt : ∀ {m : ℕ} (α : Fin m → ℕ) {N c : ℕ}, ∑ j : Fin m, α j = N → c < N →
    modeOf54 α c < m
  modeOf_spec : ∀ {m : ℕ} (α : Fin m → ℕ) {N c : ℕ} (hN : ∑ j : Fin m, α j = N) (hc : c < N),
    let i : Fin m := ⟨modeOf54 α c, modeOf_lt α hN hc⟩
    exclPrefSum54 α i ≤ c ∧ c < prefSum54 α i
  modeOf_eq_iff : ∀ {m : ℕ} (α : Fin m → ℕ) {N c : ℕ}, ∑ j : Fin m, α j = N → c < N →
    ∀ r : Fin m, modeOf54 α c = r.1 ↔ exclPrefSum54 α r ≤ c ∧ c < prefSum54 α r
  modeOf_count : ∀ {m : ℕ} (α : Fin m → ℕ) {N : ℕ}, ∑ j : Fin m, α j = N →
    ∀ r : Fin m, (Finset.univ.filter fun c : Fin N => modeOf54 α c.1 = r.1).card = α r
  modeOf_mono : ∀ {m : ℕ} (α : Fin m → ℕ), Monotone (modeOf54 α)
  wtilde2_length : ∀ {m : ℕ} (α : Fin m → ℕ) (N : ℕ), (wtilde2_54 α N).length = m + N
  wtilde3_length : ∀ {m : ℕ} (α : Fin m → ℕ) (N : ℕ), (wtilde3_54 α N).length = m + N
  wtilde8_length : ∀ {m : ℕ} (α : Fin m → ℕ) (N : ℕ), (wtilde8_54 α N).length = m + N
  wtildef_length : ∀ {m : ℕ} (α : Fin m → ℕ) (N : ℕ), (wtildef_54 α N).length = m + N
  wtilde3_pos_spec : ∀ {m : ℕ} (α : Fin m → ℕ) {N : ℕ}, ∑ j : Fin m, α j = N →
    ∀ (pos : ℕ) (hpos : pos < (wtilde3_54 α N).length),
      let t := (wtilde3_54 α N)[pos]
      (t.1 = m → t.2.2 < N ∧ pos ≥ t.2.2 ∧ pos - t.2.2 = modeOf54 α t.2.2) ∧
      (t.1 < m → ∃ hi : t.1 < m, t.2.2 = prefSum54 α ⟨t.1, hi⟩ ∧ pos ≥ t.1 ∧ pos - t.1 = t.2.2)
  wtilde8_pos_spec : ∀ {m : ℕ} (α : Fin m → ℕ) {N : ℕ}, ∑ j : Fin m, α j = N →
    ∀ (pos : ℕ) (hpos : pos < (wtilde8_54 α N).length),
      let t := (wtilde8_54 α N)[pos]
      (t.1 < m → ∃ hi : t.1 < m, t = (t.1, t.1, 0) ∧ pos ≥ t.1 ∧ pos - t.1 = prefSum54 α ⟨t.1, hi⟩) ∧
      (t.1 = m → t.2.2 < N ∧ t = (m, modeOf54 α t.2.2, t.2.2))
  wtilde2_sort_prefix : ∀ {m : ℕ} (α : Fin m → ℕ) {N : ℕ}, ∑ j : Fin m, α j = N →
    ∀ (M : ℕ) (x : Fin M → Sec5Rec54) (s_x : Fin M → Sec5Rec54) (_hM : m + N ≤ M),
      (∀ (pos : ℕ) (hpos : pos < m + N), x ⟨pos, by omega⟩ = (wtilde2_54 α N)[pos]'(by rw [wtilde2_length]; exact hpos)) →
      (∀ (pos : ℕ) (hpos : pos < M), m + N ≤ pos → (x ⟨pos, hpos⟩).2.2 = N + 1) →
      (List.ofFn s_x).Perm (List.ofFn x) →
      Monotone (keyW3_54 ∘ s_x) →
      ∀ (pos : ℕ) (hpos : pos < m + N),
        s_x ⟨pos, by omega⟩ = (wtilde3_54 α N)[pos]'(by rw [wtilde3_length]; exact hpos)
  wtildef_sort_prefix : ∀ {m : ℕ} (α : Fin m → ℕ) {N : ℕ}, ∑ j : Fin m, α j = N →
    ∀ (M : ℕ) (x : Fin M → Sec5Rec54) (s_x : Fin M → Sec5Rec54) (_hM : m + N ≤ M),
      (∀ (pos : ℕ) (hpos : pos < m + N), x ⟨pos, by omega⟩ = (wtildef_54 α N)[pos]'(by rw [wtildef_length]; exact hpos)) →
      (∀ (pos : ℕ) (hpos : pos < M), m + N ≤ pos → (x ⟨pos, hpos⟩).2.1 = m) →
      (List.ofFn s_x).Perm (List.ofFn x) →
      Monotone (keyW8_0_54 m ∘ s_x) →
      ∀ (pos : ℕ) (hpos : pos < m + N),
        s_x ⟨pos, by omega⟩ = (wtilde8_54 α N)[pos]'(by rw [wtilde8_length]; exact hpos)
  permMat_id : ∀ {ι : Type} [DecidableEq ι], permMat (id : ι → ι) = 1
  permMat_mul : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → ι),
    permMat f * permMat g = permMat (f ∘ g)
  seqClean_perm : ∀ {main anc₁ anc₂ : ℕ}
      (lc₁ : LayeredCircuit (main + anc₁)) (lc₂ : LayeredCircuit (main + anc₂))
      {f g : Qubits main → Qubits main},
    lc₁.ImplementsOnClean (permMat f) → lc₂.ImplementsOnClean (permMat g) →
    (seqClean lc₁ lc₂).ImplementsOnClean (permMat (g ∘ f))
  adj_implementsOnClean_perm : ∀ {main anc : ℕ} (lc : LayeredCircuit (main + anc))
      {f g : Qubits main → Qubits main},
    (∀ x, g (f x) = x) → (∀ x, f (g x) = x) →
    lc.ImplementsOnClean (permMat f) → lc.adj.ImplementsOnClean (permMat g)
  act_mapWires_perm : ∀ {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
      (f : Qubits main → Qubits main),
    lc.ImplementsOnClean (permMat f) →
    ∀ (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
      (_hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false),
      let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
      act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain)))
  act_subReg_perm : ∀ {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
      (f : Qubits main → Qubits main),
    lc.ImplementsOnClean (permMat f) →
    ∀ (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
      (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
      (_hclean : ∀ j : Fin anc, z (embAnc j) = false),
      act (lc.mapWires (combineEmb54 embMain embAnc hdisj)).unitary (ket z) =
        ket (updateOn embMain z (f (z ∘ embMain)))
  padZero_val_lt : ∀ {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)) (h : u.1 < main),
    padZero main anc x u = x ⟨u.1, h⟩
  padZero_val_ge : ∀ {main anc : ℕ} (x : Qubits main) (u : Fin (main + anc)),
    main ≤ u.1 → padZero main anc x u = false
  bitsToNatLSB_rev : ∀ {q : ℕ} (b : Qubits q),
    bitsToNatLSB (fun j : Fin q => b j.rev) = bitsToNat b
  natToBits_eq_rev_natToBitsLSB : ∀ (q k : ℕ), k < 2 ^ q →
    (fun j : Fin q => natToBits q k j.rev) = natToBitsLSB q k
  natToBits_apply : ∀ {q k : ℕ}, k < 2 ^ q → ∀ i : Fin q,
    natToBits q k i = natToBitsLSB q k i.rev
  bitsToNatLSB_all_false : ∀ (w : ℕ), bitsToNatLSB (fun _ : Fin w => false) = 0
  copyRegCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 0)
  copyRegCircuit_size : ∀ w : ℕ, (copyRegCircuit w).size = w
  copyRegCircuit_implements : ∀ w : ℕ,
    (copyRegCircuit w).ImplementsOnClean (permMat (copyRegFn54 w))
  setConstCircuit : (w c : ℕ) → LayeredCircuit (w + 0)
  setConstCircuit_size : ∀ w c : ℕ, (setConstCircuit w c).size ≤ w
  setConstCircuit_implements : ∀ w c : ℕ,
    (setConstCircuit w c).ImplementsOnClean (permMat (setConstFn54 w c))
  eqConstCircuit : (w c : ℕ) → LayeredCircuit ((w + 1) + w)
  eqConstCircuit_size : ∀ w c : ℕ, (eqConstCircuit w c).size ≤ 14 * w + 12
  eqConstCircuit_implements : ∀ w c : ℕ,
    (eqConstCircuit w c).ImplementsOnClean (permMat (eqConstFn54 w c))
  addInPlaceCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 1)
  addInPlaceCircuit_size : ∀ w : ℕ, (addInPlaceCircuit w).size = 14 * w
  addInPlaceCircuit_implements : ∀ w : ℕ,
    (addInPlaceCircuit w).ImplementsOnClean (permMat (addInPlaceFn54 w))
  subInPlaceCircuit : (w : ℕ) → LayeredCircuit ((w + w) + 1)
  subInPlaceCircuit_size : ∀ w : ℕ, (subInPlaceCircuit w).size = 14 * w
  subInPlaceCircuit_implements : ∀ w : ℕ,
    (subInPlaceCircuit w).ImplementsOnClean (permMat (subInPlaceFn54 w))
  ctrlCopyRegCircuit : (w : ℕ) → LayeredCircuit ((1 + w + w) + 0)
  ctrlCopyRegCircuit_size : ∀ w : ℕ, (ctrlCopyRegCircuit w).size = 5 * w
  ctrlCopyRegCircuit_implements : ∀ w : ℕ,
    (ctrlCopyRegCircuit w).ImplementsOnClean (permMat (ctrlCopyRegFn54 w))
  encodeParticleSym54Circuit : (n s : ℕ) → (s = Nat.clog 2 n + 1) → LayeredCircuit (s + (s - 1))
  encodeParticleSym54Circuit_size : ∀ (n s : ℕ) (hs : s = Nat.clog 2 n + 1),
    (encodeParticleSym54Circuit n s hs).size ≤ 13 * s
  encodeParticleSym54Circuit_act : ∀ (n s : ℕ) (_hn : 1 ≤ n) (hs : s = Nat.clog 2 n + 1)
      (j : Fin (n + 1)),
    act (encodeParticleSym54Circuit n s hs).unitary (ket (padZero s (s - 1) (natToBits s j.1))) =
      ket (padZero s (s - 1) (particleSym54 n s j))

end QuantumLTF.Membership.Supplement


