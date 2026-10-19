-- Prove2me | Definitions.Def_QAlgorithms_Defs_CircuitResources
-- name    : QAlgorithms_Defs_CircuitResources
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:24.507315+00:00
-- url     : https://prove2.me/theorems/4ff02680-4ab2-4661-af00-cf141864eca2
-- title:
--   Qubit block-encodings, clean ancillas, refined resource counts, the indexed-SWAP gate
-- statement:
--   # Qubit block-encodings, clean ancillas, refined resource counts, the indexed-SWAP gate
--   (shared definition layer)
--
--   * A. Gilyén, Y. Su, G. H. Low, N. Wiebe, *Quantum singular value transformation and beyond*
--     (arXiv:1806.01838v1), cited "GSLW p.N" (PDF pages): Definition 43 and §4.1.
--   * arXiv:2207.08800v1, cited "2207.08800 p.N" (PDF pages): §2.1, the gate set with the QRAM-like
--     indexed-SWAP gate.
--
--   Conventions are the frozen ones: `Qubits n = Fin n → Bool`, wire `0` the most significant bit,
--   `qubitsAppendEquiv a b` splits `Qubits (a + b)` into its first `a` and last `b` wires.
--   -/
--
--   namespace QAlgorithms
--
--   /-- GSLW Definition 43 (p.41), on a qubit register: the `(a + s)`-qubit `U` is an
--   `(α, a, ε)`-block-encoding of the `s`-qubit operator `A` iff `U` is unitary, `α ≥ 0` (the source's
--   `α ∈ ℝ₊`) and `‖A − α (⟨0|^{⊗a} ⊗ I) U (|0⟩^{⊗a} ⊗ I)‖ ≤ ε` (operator norm). The `a` encoding
--   ancillas are the **first** `a` wires, as in the frozen `IsBlockEncoding` (whose difference
--   `α·block − A` has the same norm).
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CircuitResources.lean

import Definitions.Def_QAlgorithms_Defs_FTCircuit
/-!
# Qubit block-encodings, clean ancillas, refined resource counts, the indexed-SWAP gate
(shared definition layer)

* A. Gilyén, Y. Su, G. H. Low, N. Wiebe, *Quantum singular value transformation and beyond*
  (arXiv:1806.01838v1), cited "GSLW p.N" (PDF pages): Definition 43 and §4.1.
* arXiv:2207.08800v1, cited "2207.08800 p.N" (PDF pages): §2.1, the gate set with the QRAM-like
  indexed-SWAP gate.

Conventions are the frozen ones: `Qubits n = Fin n → Bool`, wire `0` the most significant bit,
`qubitsAppendEquiv a b` splits `Qubits (a + b)` into its first `a` and last `b` wires.
-/

namespace QAlgorithms

/-- GSLW Definition 43 (p.41), on a qubit register: the `(a + s)`-qubit `U` is an
`(α, a, ε)`-block-encoding of the `s`-qubit operator `A` iff `U` is unitary, `α ≥ 0` (the source's
`α ∈ ℝ₊`) and `‖A − α (⟨0|^{⊗a} ⊗ I) U (|0⟩^{⊗a} ⊗ I)‖ ≤ ε` (operator norm). The `a` encoding
ancillas are the **first** `a` wires, as in the frozen `IsBlockEncoding` (whose difference
`α·block − A` has the same norm). -/
def IsQubitBlockEncoding (a s : ℕ) (U : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ) (α ε : ℝ)
    (A : Matrix (Qubits s) (Qubits s) ℂ) : Prop :=
  0 ≤ α ∧ IsBlockEncoding (fun _ : Fin a => false)
    (U.submatrix (qubitsAppendEquiv a s).symm (qubitsAppendEquiv a s).symm) α ε A

/-- The vector `ψ ⊗ |0^w⟩`: `w` clean ancillas in `|0⟩` appended **after** the `m` wires of `ψ`
(GSLW p.41, "purely ancillary qubits"). Vector counterpart of the frozen `withZeroAncillas`. -/
noncomputable def zeroAncillaVec {m : ℕ} (ψ : EuclideanSpace ℂ (Qubits m)) (w : ℕ) :
    EuclideanSpace ℂ (Qubits (m + w)) :=
  WithLp.toLp 2 fun z =>
    if (qubitsAppendEquiv m w z).2 = (fun _ => false) then ψ (qubitsAppendEquiv m w z).1 else 0

/-- GSLW p.41 (§4.2): `M` implements the `m`-qubit operator `V` using `w` purely ancillary qubits,
which start in `|0⟩` and are returned exactly to `|0⟩` for every input: `M (ψ ⊗ |0^w⟩) =
(Vψ) ⊗ |0^w⟩` (exact equality, no global phase). -/
def ImplementsWithCleanAncillas {m w : ℕ} (M : Matrix (Qubits (m + w)) (Qubits (m + w)) ℂ)
    (V : Matrix (Qubits m) (Qubits m) ℂ) : Prop :=
  ∀ ψ : EuclideanSpace ℂ (Qubits m), act M (zeroAncillaVec ψ w) = zeroAncillaVec (act V ψ) w

/-- The number of **uncontrolled** query steps to oracle `k` (uses of `U` or `U†`) in a frozen
`OracleCircuit` (GSLW Theorem 56, p.48, and Corollary 62, p.53, count uses of `U`, `U†` and their
controlled versions separately). -/
def OracleCircuit.plainQueryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (k : Fin r) : ℕ :=
  c.countP fun s => match s with
    | .query k' _ none _ _ => decide (k' = k)
    | _ => false

/-- The number of **controlled** query steps to oracle `k` (controlled `U` or `U†`) in a frozen
`OracleCircuit` (GSLW Theorem 56, p.48; Corollary 62, p.53). -/
def OracleCircuit.controlledQueryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (k : Fin r) : ℕ :=
  c.countP fun s => match s with
    | .query k' _ (some _) _ _ => decide (k' = k)
    | _ => false

/-- The number of non-query gates of a frozen `OracleCircuit` whose gate satisfies `P`
(2207.08800 p.6 §2.1 and Proposition 22, p.22, count indexed-SWAP gates and "additional" gates
separately). -/
noncomputable def OracleCircuit.gateCountWhere {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : OracleCircuit S a n) (P : Gate → Prop) : ℕ :=
  c.countP fun s => match s with
    | .gate g => @decide (P g.gate) (Classical.propDecidable _)
    | .query _ _ _ _ _ => false

/-- The basis map of the indexed-SWAP gate on `d` memory qubits (2207.08800 p.6):
`|i⟩|j⟩|x_1 … x_d⟩ ↦ |i⟩|j⟩ SWAP_{i,j}|x_1 … x_d⟩`. The register is two index registers of
`⌈log₂ d⌉` qubits (`i` first) followed by the `d` memory qubits. Indices are the source's
`[d] = {0, …, d − 1}`: index value `i` (read most significant bit first) names memory wire `i`.
For index values `≥ d`, which the source leaves unspecified, the map is the identity. -/
def indexedSwapMap (d : ℕ) (z : Qubits (Nat.clog 2 d + Nat.clog 2 d + d)) :
    Qubits (Nat.clog 2 d + Nat.clog 2 d + d) :=
  if h : bitsToNat (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 d)
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1).1 < d ∧
      bitsToNat (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 d)
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1).2 < d then
    (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d).symm
      ((qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1,
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).2 ∘
          Equiv.swap ⟨_, h.1⟩ ⟨_, h.2⟩)
  else z

/-- The indexed-SWAP gate acting on `d` bits (2207.08800 p.6, §2.1), as a frozen `Gate` on
`2⌈log₂ d⌉ + d` qubits: the permutation matrix of `indexedSwapMap d`. -/
def indexedSwapGate (d : ℕ) : Gate :=
  ⟨Nat.clog 2 d + Nat.clog 2 d + d, Matrix.of fun y z => if y = indexedSwapMap d z then 1 else 0⟩

/-- The gate set of 2207.08800 §2.1 (p.6): all single-qubit (unitary) gates, CNOT, and the
indexed-SWAP gates on `d ≥ 1` memory qubits. -/
def vacgnGateSet : Set Gate :=
  {g | ∃ M : Matrix Bool Bool ℂ, M ∈ Matrix.unitaryGroup Bool ℂ ∧ g = Gate.ofMatrix1 M} ∪
    {Gate.ofMatrix2 cnot} ∪ {g | ∃ d, 1 ≤ d ∧ g = indexedSwapGate d}

/-! ### Sanity tests -/

theorem OracleCircuit.queryCount_eq_plain_add_controlled {S : Set Gate} {r : ℕ} {a : Fin r → ℕ}
    {n : ℕ} (c : OracleCircuit S a n) (k : Fin r) :
    c.queryCount k = c.plainQueryCount k + c.controlledQueryCount k := by
  induction c with
  | nil => rfl
  | cons s c ih =>
    simp only [OracleCircuit.queryCount, OracleCircuit.plainQueryCount,
      OracleCircuit.controlledQueryCount, List.countP_cons] at ih ⊢
    rw [ih]
    rcases s with g | ⟨k', adj, ctl, w, hc⟩
    · simp [OracleStep.IsQueryTo]
    · cases ctl <;> by_cases h : k' = k <;> simp [OracleStep.IsQueryTo, h] <;> omega

example {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    ImplementsWithCleanAncillas (w := 0) (1 : Matrix (Qubits (n + 0)) (Qubits (n + 0)) ℂ)
      (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  intro φ
  simp [act]

theorem indexedSwapMap_involutive (d : ℕ) (z : Qubits (Nat.clog 2 d + Nat.clog 2 d + d)) :
    indexedSwapMap d (indexedSwapMap d z) = z := by
  unfold indexedSwapMap
  by_cases h : bitsToNat (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 d)
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1).1 < d ∧
      bitsToNat (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 d)
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1).2 < d
  · rw [dif_pos h]
    simp only [Equiv.apply_symm_apply]
    rw [dif_pos h]
    rw [Equiv.symm_apply_eq]
    ext i
    · rfl
    · simp [Function.comp_def, Equiv.swap_apply_self]
  · rw [dif_neg h, dif_neg h]

example (d : ℕ) (z : Qubits (Nat.clog 2 d + Nat.clog 2 d + d))
    (h : ¬ bitsToNat (qubitsAppendEquiv (Nat.clog 2 d) (Nat.clog 2 d)
        (qubitsAppendEquiv (Nat.clog 2 d + Nat.clog 2 d) d z).1).1 < d) :
    indexedSwapMap d z = z := by
  unfold indexedSwapMap
  rw [dif_neg (fun h' => h h'.1)]

example : (indexedSwapGate 1).arity = 1 := by
  simp [indexedSwapGate]

example : Gate.ofMatrix2 cnot ∈ vacgnGateSet :=
  Set.mem_union_left _ (Set.mem_union_right _ rfl)

end QAlgorithms


