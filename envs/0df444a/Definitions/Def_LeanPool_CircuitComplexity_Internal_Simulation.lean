-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_Simulation
-- name    : LeanPool_CircuitComplexity_Internal_Simulation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:12:10.6022+00:00
-- url     : https://prove2.me/theorems/63124255-733b-4390-94c5-637e2672167e
-- title:
--   Simulation
-- statement:
--   Definitions and structural lemmas for Simulation, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Simulation.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_AON
public import Theorems.Thm_CircuitComplexity_AONOp_eval_two_and
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
public import Theorems.Thm_CircuitComplexity_CompleteBasis_of_simulation
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
def AONOp.dual : AONOp → AONOp
  | .and => .or
  | .or => .and
def AONOp.identity : AONOp → Bool
  | .and => true
  | .or => false
def AONOp.binOp : AONOp → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)
lemma AONOp.eval_eq_foldl (op : AONOp) (n : Nat) (v : BitString n) :
    op.eval n v = Fin.foldl n (fun acc i => op.binOp acc (v i)) op.identity := by
  cases op <;> rfl
lemma AONOp.identity_binOp (op : AONOp) (b : Bool) : op.binOp op.identity b = b := by
  cases op <;> simp [AONOp.binOp, AONOp.identity]
lemma AONOp.dual_const (op : AONOp) (b : Bool) :
    op.dual.eval 2 (fun i => (if i.val = 0 then false else true).xor b) =
    op.identity := by
  cases op <;> cases b <;>
    simp [AONOp.dual, AONOp.identity, AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]
lemma AONOp.passthrough_eq (op : AONOp) (v : Bool) :
    op.eval 2 (fun _ => v) = v := by
  cases op <;> cases v <;>
    simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]
namespace CompileAON
def chainLen (k : Nat) : Nat := if k ≤ 1 then 1 else k - 1
@[simp] lemma chainLen_zero : chainLen 0 = 1 := rfl
@[simp] lemma chainLen_one : chainLen 1 = 1 := rfl
lemma chainLen_pos (k : Nat) : 0 < chainLen k := by
  unfold chainLen; split <;> omega
lemma chainLen_of_ge_two {k : Nat} (hk : 2 ≤ k) : chainLen k = k - 1 := by
  rw [chainLen, if_neg (by omega)]
def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSum f n + f n
@[simp] lemma prefixSum_zero' (f : Nat → Nat) : prefixSum f 0 = 0 := rfl
lemma prefixSum_succ (f : Nat → Nat) (n : Nat) :
    prefixSum f (n + 1) = prefixSum f n + f n := rfl
lemma prefixSum_mono (f : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    prefixSum f i ≤ prefixSum f j := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ ih => rw [prefixSum_succ]; omega
def segLookup (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    Nat × Nat :=
  match n with
  | 0 => absurd h (by simp)
  | n + 1 =>
    if hlt : idx < prefixSum f n then segLookup n f idx hlt
    else (n, idx - prefixSum f n)
lemma segLookup_fst_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).1 < n := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact Nat.lt_succ_of_lt (ih _)
    · exact Nat.lt_succ_of_le (Nat.le_refl n)
lemma segLookup_snd_lt (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    (segLookup n f idx h).2 < f (segLookup n f idx h).1 := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · dsimp only
      rw [prefixSum_succ] at h; omega
lemma segLookup_sum (n : Nat) (f : Nat → Nat) (idx : Nat) (h : idx < prefixSum f n) :
    prefixSum f (segLookup n f idx h).1 + (segLookup n f idx h).2 = idx := by
  induction n with
  | zero => simp [prefixSum] at h
  | succ n ih =>
    simp only [segLookup]
    split
    · exact ih _
    · dsimp only; omega
variable {N M G : Nat} [NeZero N] [NeZero M]
def iChainF (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  if h : i < G then chainLen (c.gates ⟨i, h⟩).fanIn else 0
def oChainF (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  if h : j < M then chainLen (c.outputs ⟨j, h⟩).fanIn else 0
def iTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (iChainF c) G
def oTotal (c : Circuit Basis.unboundedAON N M G) : Nat := prefixSum (oChainF c) M
def G' (c : Circuit Basis.unboundedAON N M G) : Nat := iTotal c + oTotal c
def iOffset (c : Circuit Basis.unboundedAON N M G) (i : Nat) : Nat :=
  prefixSum (iChainF c) i
def oOffset (c : Circuit Basis.unboundedAON N M G) (j : Nat) : Nat :=
  iTotal c + prefixSum (oChainF c) j
lemma iChainF_eq (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iChainF c i = chainLen (c.gates ⟨i, hi⟩).fanIn := by simp [iChainF, hi]
lemma oChainF_eq (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oChainF c j = chainLen (c.outputs ⟨j, hj⟩).fanIn := by simp [oChainF, hj]
lemma iOffset_succ (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c (i + 1) = iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn := by
  simp [iOffset, prefixSum_succ, iChainF, hi]
lemma iOffset_chain_le_iTotal (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn ≤ iTotal c := by
  rw [← iOffset_succ c hi]; exact prefixSum_mono _ (by omega)
lemma oOffset_chain_le_G' (c : Circuit Basis.unboundedAON N M G) {j : Nat} (hj : j < M) :
    oOffset c j + chainLen (c.outputs ⟨j, hj⟩).fanIn ≤ G' c := by
  suffices h : prefixSum (oChainF c) j + chainLen (c.outputs ⟨j, hj⟩).fanIn
      ≤ prefixSum (oChainF c) M by unfold oOffset G' iTotal oTotal at *; omega
  rw [← oChainF_eq c hj, ← prefixSum_succ]
  exact prefixSum_mono _ (by omega)
def remapWire (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G)) :
    Fin (N + G' c) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else
    have hi : w.val - N < G := by omega
    have hle := iOffset_chain_le_iTotal c hi
    have hpos := chainLen_pos (c.gates ⟨w.val - N, hi⟩).fanIn
    ⟨N + iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, hi⟩).fanIn - 1, by
      unfold G'; omega⟩
lemma remapWire_input (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    (hw : w.val < N) : (remapWire c w).val = w.val := by
  simp [remapWire, hw]
lemma remapWire_gate (c : Circuit Basis.unboundedAON N M G) {i : Nat} (hi : i < G) :
    (remapWire c ⟨N + i, by omega⟩).val =
      N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1 := by
  unfold remapWire
  simp [show ¬(N + i < N) from by omega]
lemma remapWire_lt_of_lt (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    {i : Nat} (hi : i ≤ G) (hw : w.val < N + i) :
    (remapWire c w).val < N + iOffset c i := by
  unfold remapWire
  split
  · simp [iOffset]; omega
  · rename_i hNotLt
    push Not at hNotLt
    have hwN : w.val - N < i := by omega
    simp only []
    have key : iOffset c (w.val - N) + chainLen (c.gates ⟨w.val - N, by omega⟩).fanIn
        ≤ iOffset c i := by
      rw [← iOffset_succ c (by omega : w.val - N < G)]
      exact prefixSum_mono _ (by omega)
    have := chainLen_pos (c.gates ⟨w.val - N, by omega⟩).fanIn
    omega
lemma remapWire_lt_oOffset (c : Circuit Basis.unboundedAON N M G) (w : Fin (N + G))
    (j : Nat) : (remapWire c w).val < N + oOffset c j := by
  have h := remapWire_lt_of_lt c w (Nat.le.refl) w.isLt
  have : iOffset c G = iTotal c := rfl
  unfold oOffset at *; omega
def fin2 (a b : α) : Fin 2 → α := fun i => if i.val = 0 then a else b
@[simp] lemma fin2_zero (a b : α) : fin2 a b 0 = a := rfl
@[simp] lemma fin2_one (a b : α) : fin2 a b 1 = b := rfl
def mkChainOp (op : AONOp) (k : Nat) : AONOp :=
  if k = 0 then op.dual else op
def mkChainInputs {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat)
    (hj : j < chainLen k) (hbase : base + chainLen k ≤ W) : Fin 2 → Fin W :=
  if hk0 : k = 0 then fun _ => ⟨0, hW⟩
  else if hk1 : k = 1 then fun _ => ri ⟨0, by omega⟩
  else if hj0 : j = 0 then fin2 (ri ⟨0, by omega⟩) (ri ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    have : j + 1 < k := by omega
    have : 1 ≤ j := by omega
    fin2 ⟨base + j - 1, by omega⟩ (ri ⟨j + 1, by omega⟩)
def mkChainNeg (k : Nat) (rn : Fin k → Bool) (j : Nat)
    (hj : j < chainLen k) : Fin 2 → Bool :=
  if hk0 : k = 0 then fin2 false true
  else if hk1 : k = 1 then fun _ => rn ⟨0, by omega⟩
  else if _ : j = 0 then fin2 (rn ⟨0, by omega⟩) (rn ⟨1, by omega⟩)
  else
    have : 2 ≤ k := by omega
    have : chainLen k = k - 1 := chainLen_of_ge_two ‹_›
    fin2 false (rn ⟨j + 1, by omega⟩)
def mkChainGate {W : Nat} (hW : 0 < W) (op : AONOp) (k : Nat)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W) : Gate Basis.andOr2 W :=
  { op := mkChainOp op k, fanIn := 2, arityOk := rfl,
    inputs := mkChainInputs hW k ri base j hj hbase,
    negated := mkChainNeg k rn j hj }
lemma mkChainInputs_lt {W : Nat} (hW : 0 < W) (k : Nat)
    (ri : Fin k → Fin W) (base : Nat) (j : Nat) (hj : j < chainLen k)
    (hbase : base + chainLen k ≤ W)
    (hri_lt : ∀ i, (ri i).val < base) (hbase_pos : 0 < base)
    (i : Fin 2) :
    (mkChainInputs hW k ri base j hj hbase i).val < base + j := by
  simp only [mkChainInputs]
  split_ifs with hk0 hk1 hj0
  · dsimp only; omega
  · exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)
  · simp only [fin2]; split_ifs
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
    · exact Nat.lt_of_lt_of_le (hri_lt _) (by omega)
  · simp only [fin2]; split_ifs
    · dsimp only; omega
    · exact Nat.lt_of_lt_of_le (hri_lt _) (Nat.le_add_right _ _)
def compileGateInputs (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Fin (N + G' c) :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainInputs (by omega) (c.gates ⟨seg.1, hi⟩).fanIn
      (fun i => remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i))
      (N + iOffset c seg.1) seg.2 hj
      (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainInputs (by omega) (c.outputs ⟨seg.1, hj⟩).fanIn
      (fun i => remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i))
      (N + oOffset c seg.1) seg.2 hk
      (by have := oOffset_chain_le_G' c hj; omega)
def compileGateOp (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) : AONOp :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    mkChainOp (c.gates ⟨seg.1, hi⟩).op (c.gates ⟨seg.1, hi⟩).fanIn
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    mkChainOp (c.outputs ⟨seg.1, hj⟩).op (c.outputs ⟨seg.1, hj⟩).fanIn
def compileGateNeg (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Fin 2 → Bool :=
  if h : idx.val < iTotal c then
    let seg := segLookup G (iChainF c) idx.val h
    have hi : seg.1 < G := segLookup_fst_lt G _ _ h
    have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
      rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
    mkChainNeg (c.gates ⟨seg.1, hi⟩).fanIn (c.gates ⟨seg.1, hi⟩).negated seg.2 hj
  else
    have hoff : idx.val - iTotal c < oTotal c := by
      have := idx.isLt; unfold G' at this; omega
    let seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff
    have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
    have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
      rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
    mkChainNeg (c.outputs ⟨seg.1, hj⟩).fanIn (c.outputs ⟨seg.1, hj⟩).negated seg.2 hk
def compileGates (c : Circuit Basis.unboundedAON N M G) (idx : Fin (G' c)) :
    Gate Basis.andOr2 (N + G' c) :=
  { op := compileGateOp c idx, fanIn := 2, arityOk := rfl,
    inputs := compileGateInputs c idx,
    negated := compileGateNeg c idx }
def compileOutputs (c : Circuit Basis.unboundedAON N M G) (j : Fin M) :
    Gate Basis.andOr2 (N + G' c) :=
  let lastWire : Fin (N + G' c) :=
    ⟨N + oOffset c j.val + chainLen (c.outputs j).fanIn - 1, by
      have hle : oOffset c j.val + chainLen (c.outputs j).fanIn ≤ G' c :=
        oOffset_chain_le_G' c j.isLt
      have hpos := chainLen_pos (c.outputs j).fanIn
      omega⟩
  { op := .and, fanIn := 2, arityOk := rfl,
    inputs := fun _ => lastWire, negated := fun _ => false }
def compileFn (c : Circuit Basis.unboundedAON N M G) : Circuit Basis.andOr2 N M (G' c) where
  gates := compileGates c
  outputs := compileOutputs c
  acyclic := by
    intro idx k
    change (compileGateInputs c idx k).val < N + idx.val
    have hN : 0 < N := by have := NeZero.ne N; omega
    unfold compileGateInputs
    split
    case isTrue h =>
      -- Internal region: idx.val < iTotal c
      set seg := segLookup G (iChainF c) idx.val h with hseg_def
      have hi : seg.1 < G := segLookup_fst_lt G _ _ h
      have hj : seg.2 < chainLen (c.gates ⟨seg.1, hi⟩).fanIn := by
        rw [← iChainF_eq c hi]; exact segLookup_snd_lt G _ _ h
      have hsum : prefixSum (iChainF c) seg.1 + seg.2 = idx.val :=
        segLookup_sum G _ _ h
      have hiOff : iOffset c seg.1 = prefixSum (iChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.gates ⟨seg.1, hi⟩).inputs i)).val <
          N + iOffset c seg.1 :=
        fun i => remapWire_lt_of_lt c _ (by omega) (c.acyclic ⟨seg.1, hi⟩ i)
      have hbase_eq : N + iOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hiOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hj
        (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)
        hri_lt (by omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)
    case isFalse h =>
      -- Output region: idx.val ≥ iTotal c
      have hoff : idx.val - iTotal c < oTotal c := by
        have := idx.isLt; unfold G' at this; omega
      set seg := segLookup M (oChainF c) (idx.val - iTotal c) hoff with hseg_def
      have hj : seg.1 < M := segLookup_fst_lt M _ _ hoff
      have hk : seg.2 < chainLen (c.outputs ⟨seg.1, hj⟩).fanIn := by
        rw [← oChainF_eq c hj]; exact segLookup_snd_lt M _ _ hoff
      have hsum : prefixSum (oChainF c) seg.1 + seg.2 = idx.val - iTotal c :=
        segLookup_sum M _ _ hoff
      have hoOff : oOffset c seg.1 = iTotal c + prefixSum (oChainF c) seg.1 := rfl
      have hri_lt : ∀ i, (remapWire c ((c.outputs ⟨seg.1, hj⟩).inputs i)).val <
          N + oOffset c seg.1 :=
        fun i => remapWire_lt_oOffset c _ seg.1
      have hbase_eq : N + oOffset c seg.1 + seg.2 = N + idx.val := by
        rw [hoOff]; omega
      have hlt := mkChainInputs_lt (by omega) _ _ _ seg.2 hk
        (by have := oOffset_chain_le_G' c hj; omega)
        hri_lt (by rw [hoOff]; omega) k
      exact Nat.lt_of_lt_of_le hlt (by omega)
lemma segLookup_of_prefixSum (n : Nat) (f : Nat → Nat) (i j : Nat)
    (hi : i < n) (hj : j < f i)
    (h : prefixSum f i + j < prefixSum f n) :
    segLookup n f (prefixSum f i + j) h = (i, j) := by
  induction n with
  | zero => omega
  | succ n ihn =>
    simp only [segLookup]
    by_cases hlt : prefixSum f i + j < prefixSum f n
    · have hin : i < n := by
        by_contra h'; have := prefixSum_mono f (show n ≤ i by omega); omega
      simp [hlt, ihn hin hlt]
    · have : i = n := by
        by_contra h'
        have := prefixSum_mono f (by omega : i + 1 ≤ n)
        rw [prefixSum_succ] at this; omega
      simp_all
def partialFold (op : AONOp) (v : Fin k → Bool) (j : Nat) : Bool :=
  if h : j ≤ k then
    Fin.foldl j (fun acc i => op.binOp acc (v ⟨i.val, by omega⟩)) op.identity
  else op.eval k v
lemma partialFold_zero (op : AONOp) (v : Fin k → Bool) :
    partialFold op v 0 = op.identity := by
  simp [partialFold, Fin.foldl_zero]
lemma partialFold_succ (op : AONOp) (v : Fin k → Bool) (j : Nat) (hj : j < k) :
    partialFold op v (j + 1) = op.binOp (partialFold op v j) (v ⟨j, hj⟩) := by
  simp only [partialFold, show j + 1 ≤ k from by omega, show j ≤ k from by omega, dite_true]
  rw [Fin.foldl_succ_last]; congr 1
lemma partialFold_one (op : AONOp) (v : Fin k → Bool) (hk : 0 < k) :
    partialFold op v 1 = op.binOp op.identity (v ⟨0, hk⟩) := by
  rw [partialFold_succ op v 0 hk, partialFold_zero]
lemma partialFold_two (op : AONOp) (v : Fin k → Bool) (hk : 1 < k) :
    partialFold op v 2 = op.binOp (op.binOp op.identity (v ⟨0, by omega⟩)) (v ⟨1, hk⟩) := by
  rw [partialFold_succ op v 1 hk, partialFold_one op v (by omega)]
lemma partialFold_full (op : AONOp) (v : Fin k → Bool) :
    partialFold op v k = op.eval k v := by
  simp only [partialFold, le_refl, dite_true, AONOp.eval_eq_foldl]
lemma iSegLookup_eq (c : Circuit Basis.unboundedAON N M G)
    (i : Nat) (hi : i < G) (j : Nat) (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn)
    (h : iOffset c i + j < iTotal c := by
      have := iOffset_chain_le_iTotal c hi; omega) :
    segLookup G (iChainF c) (iOffset c i + j) h = (i, j) :=
  segLookup_of_prefixSum G (iChainF c) i j hi (by rw [iChainF_eq c hi]; exact hj) h
lemma oSegLookup_eq (c : Circuit Basis.unboundedAON N M G)
    (j' : Nat) (hj' : j' < M) (p : Nat) (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn)
    (h : prefixSum (oChainF c) j' + p < oTotal c := by
      have := oOffset_chain_le_G' c hj'; unfold G' oOffset oTotal at *; omega) :
    segLookup M (oChainF c) (prefixSum (oChainF c) j' + p) h = (j', p) :=
  segLookup_of_prefixSum M (oChainF c) j' p hj' (by rw [oChainF_eq c hj']; exact hp) h
lemma andOr2_eval (op : AONOp) (v : BitString 2) :
    op.eval 2 v = op.binOp (v 0) (v 1) := by
  cases op <;> simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero, AONOp.binOp]
lemma mkChainGate_eval_ge2_zero {W base : Nat} (op : AONOp) {k : Nat} (hk : 2 ≤ k)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (hW : 0 < W) (hj : 0 < chainLen k) (hbase : base + chainLen k ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op k ri rn base 0 hj hbase).eval wv =
    op.binOp ((rn ⟨0, by omega⟩).xor (wv (ri ⟨0, by omega⟩)))
             ((rn ⟨1, by omega⟩).xor (wv (ri ⟨1, by omega⟩))) := by
  simp only [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg]
  simp only [show ¬(k = 0) from by omega, show ¬(k = 1) from by omega, ite_false, dite_false]
  rw [andOr2_eval]; simp [fin2]
lemma mkChainGate_eval_ge2_succ {W base : Nat} (op : AONOp) {k : Nat} (hk : 2 ≤ k)
    (ri : Fin k → Fin W) (rn : Fin k → Bool)
    (hW : 0 < W) {j' : Nat} (hj : j' + 1 < chainLen k) (hbase : base + chainLen k ≤ W)
    (wv : BitString W) :
    (mkChainGate hW op k ri rn base (j' + 1) hj hbase).eval wv =
    op.binOp (wv ⟨base + j', by have := chainLen_of_ge_two hk; omega⟩)
             ((rn ⟨j' + 2, by have := chainLen_of_ge_two hk; omega⟩).xor
              (wv (ri ⟨j' + 2, by have := chainLen_of_ge_two hk; omega⟩))) := by
  simp only [mkChainGate, Gate.eval, Basis.andOr2, mkChainOp, mkChainInputs, mkChainNeg]
  simp only [show ¬(k = 0) from by omega, show ¬(k = 1) from by omega,
             show ¬(j' + 1 = 0) from by omega, ite_false, dite_false]
  rw [andOr2_eval]
  simp_all
lemma mkChainGate_gate_congr (c : Circuit Basis.unboundedAON N M G)
    {g g' : Gate Basis.unboundedAON (N + G)} {base base' j j' : Nat}
    {hW hW' : 0 < N + G' c}
    {hj : j < chainLen g.fanIn} {hj' : j' < chainLen g'.fanIn}
    {hb : base + chainLen g.fanIn ≤ N + G' c} {hb' : base' + chainLen g'.fanIn ≤ N + G' c}
    (hg : g = g') (hbase : base = base') (hjj : j = j') :
    mkChainGate hW g.op g.fanIn (fun p => remapWire c (g.inputs p)) g.negated base j hj hb =
      mkChainGate hW' g'.op g'.fanIn (fun p => remapWire c (g'.inputs p)) g'.negated
        base' j' hj' hb' := by
  subst hg
  subst hbase
  subst hjj
  rfl
lemma compileGate_eval_at_iOffset (c : Circuit Basis.unboundedAON N M G)
    (i : Nat) (hi : i < G) (j : Nat) (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn)
    (hidx : iOffset c i + j < G' c := by
      have := iOffset_chain_le_iTotal c hi; have := chainLen_pos (c.gates ⟨i, hi⟩).fanIn;
      unfold G'; omega)
    (wv : BitString (N + G' c)) :
    (compileGates c ⟨iOffset c i + j, hidx⟩).eval wv =
      (mkChainGate (by omega : 0 < N + G' c) (c.gates ⟨i, hi⟩).op (c.gates ⟨i, hi⟩).fanIn
        (fun p => remapWire c ((c.gates ⟨i, hi⟩).inputs p))
        (c.gates ⟨i, hi⟩).negated
        (N + iOffset c i) j hj
        (by have := iOffset_chain_le_iTotal c hi; unfold G'; omega)).eval wv := by
  -- The compiled gate at this index looks its gate up through `segLookup`, which returns
  -- `(i, j)`; the two chain gates then differ only in proof terms.
  have hInternal : iOffset c i + j < iTotal c := by
    have := iOffset_chain_le_iTotal c hi; omega
  have hSeg := iSegLookup_eq c i hi j hj hInternal
  have hSeg1 : (segLookup G (iChainF c) (iOffset c i + j) hInternal).1 = i := by rw [hSeg]
  have hSeg2 : (segLookup G (iChainF c) (iOffset c i + j) hInternal).2 = j := by rw [hSeg]
  unfold compileGates
  simp only [compileGateOp, compileGateInputs, compileGateNeg, Fin.val_mk,
             dif_pos hInternal, mkChainGate]
  refine congrArg (fun g => Gate.eval g wv) ?_
  exact mkChainGate_gate_congr c
    (g := c.gates ⟨(segLookup G (iChainF c) (iOffset c i + j) hInternal).1,
      segLookup_fst_lt G _ _ hInternal⟩)
    (g' := c.gates ⟨i, hi⟩)
    (congrArg c.gates (Fin.ext hSeg1)) (by rw [hSeg1]) hSeg2
theorem chainCollapse (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (gate : Gate Basis.unboundedAON (N + G)) (off : Nat)
    (hoff : 0 < N + G' c) (hbase : off + chainLen gate.fanIn ≤ G' c)
    (chain_wire : ∀ j : Nat, (hj : j < chainLen gate.fanIn) →
      (compileFn c).wireValue input ⟨N + off + j, by omega⟩ =
      (mkChainGate hoff gate.op gate.fanIn
        (fun p => remapWire c (gate.inputs p)) gate.negated
        (N + off) j hj (by omega)).eval ((compileFn c).wireValue input))
    (hv_remap : ∀ p : Fin gate.fanIn,
      (compileFn c).wireValue input (remapWire c (gate.inputs p)) =
      c.wireValue input (gate.inputs p)) :
    (compileFn c).wireValue input
      ⟨N + off + (chainLen gate.fanIn - 1), by
        have := chainLen_pos gate.fanIn; omega⟩ =
    gate.eval (c.wireValue input) := by
  rw [chain_wire (chainLen gate.fanIn - 1) (by have := chainLen_pos gate.fanIn; omega)]
  rcases Nat.eq_zero_or_pos gate.fanIn with hk0 | hk_pos
  · trans gate.op.identity
    · simp only [hk0, chainLen_zero, Nat.sub_self,
                 mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                 dite_true, Gate.eval, Basis.andOr2, fin2]
      exact AONOp.dual_const _ _
    · simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk0, Fin.foldl_zero]
  · rcases Nat.eq_or_lt_of_le hk_pos with hk1 | hk_ge2
    · have hk1' : gate.fanIn = 1 := hk1.symm
      trans (gate.negated ⟨0, by omega⟩).xor
            (c.wireValue input (gate.inputs ⟨0, by omega⟩))
      · simp only [hk1', chainLen_one, Nat.sub_self,
                   mkChainGate, mkChainOp, mkChainInputs, mkChainNeg,
                   dite_true, dite_false, Gate.eval, Basis.andOr2, AONOp.passthrough_eq,
                   show ¬(1 = 0) from by omega]
        congr 1
        exact hv_remap ⟨0, by omega⟩
      · simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl, hk1',
                   Fin.foldl_succ_last, Fin.foldl_zero, AONOp.identity_binOp]
        congr 1
    · have hcl : chainLen gate.fanIn = gate.fanIn - 1 := chainLen_of_ge_two (by omega)
      let v := fun p : Fin gate.fanIn =>
        (gate.negated p).xor (c.wireValue input (gate.inputs p))
      have hvx : ∀ p : Fin gate.fanIn,
          (gate.negated p).xor
            ((compileFn c).wireValue input (remapWire c (gate.inputs p))) = v p :=
        fun p => by rw [hv_remap p]
      have h_fold : ∀ j : Nat, (hj : j < chainLen gate.fanIn) →
          (mkChainGate hoff gate.op gate.fanIn
            (fun p => remapWire c (gate.inputs p)) gate.negated
            (N + off) j hj (by omega)).eval
            ((compileFn c).wireValue input) = partialFold gate.op v (j + 2) := by
        intro j hj
        induction j with
        | zero =>
          rw [mkChainGate_eval_ge2_zero (base := N + off) gate.op (by omega : 2 ≤ gate.fanIn)
            (fun p => remapWire c (gate.inputs p)) gate.negated hoff hj (by omega)]
          rw [hvx ⟨0, by omega⟩, hvx ⟨1, by omega⟩]
          rw [partialFold_two gate.op v (by omega)]
          rw [AONOp.identity_binOp gate.op]
        | succ j' ih =>
          rw [mkChainGate_eval_ge2_succ (base := N + off) gate.op (by omega : 2 ≤ gate.fanIn)
            (fun p => remapWire c (gate.inputs p)) gate.negated hoff hj (by omega)]
          rw [hvx ⟨j' + 2, by rw [hcl] at hj; omega⟩]
          rw [chain_wire j' (by rw [hcl] at hj ⊢; omega),
              ih (by rw [hcl] at hj ⊢; omega)]
          rw [partialFold_succ gate.op v (j' + 2) (by rw [hcl] at hj; omega)]
      rw [h_fold _ (by omega)]
      have hk_eq : chainLen gate.fanIn - 1 + 2 = gate.fanIn := by omega
      rw [hk_eq, partialFold_full gate.op v]
      simp only [Gate.eval, Basis.unboundedAON, AONOp.eval_eq_foldl]
      rfl
theorem lastChainValue_eq (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (i : Nat) (hi : i < G)
    (ih_outer : ∀ w : Fin (N + G), w.val < N + i →
      (compileFn c).wireValue input (remapWire c w) = c.wireValue input w) :
    (compileFn c).wireValue input
      ⟨N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1, by
        have := iOffset_chain_le_iTotal c hi
        have := chainLen_pos (c.gates ⟨i, hi⟩).fanIn
        unfold G'; omega⟩ =
    (c.gates ⟨i, hi⟩).eval (c.wireValue input) := by
  -- Reindex: N + x + y - 1 → N + x + (y - 1) to match chain_wire format
  have hle := iOffset_chain_le_iTotal c hi
  have hpos := chainLen_pos (c.gates ⟨i, hi⟩).fanIn
  suffices h : (compileFn c).wireValue input
      ⟨N + iOffset c i + (chainLen (c.gates ⟨i, hi⟩).fanIn - 1), by unfold G'; omega⟩ =
      (c.gates ⟨i, hi⟩).eval (c.wireValue input) by
    have heq : N + iOffset c i + chainLen (c.gates ⟨i, hi⟩).fanIn - 1 =
        N + iOffset c i + (chainLen (c.gates ⟨i, hi⟩).fanIn - 1) := by omega
    simp_all
  -- Each chain wire evaluates to its compiled gate
  have chain_wire : ∀ j : Nat, (hj : j < chainLen (c.gates ⟨i, hi⟩).fanIn) →
      (compileFn c).wireValue input ⟨N + iOffset c i + j, by unfold G'; omega⟩ =
      (mkChainGate (by unfold G'; omega : 0 < N + G' c) (c.gates ⟨i, hi⟩).op (c.gates ⟨i, hi⟩).fanIn
        (fun p => remapWire c ((c.gates ⟨i, hi⟩).inputs p)) (c.gates ⟨i, hi⟩).negated
        (N + iOffset c i) j hj (by unfold G'; omega)).eval
        ((compileFn c).wireValue input) := by
    intro j hj
    rw [Circuit.wireValue_ge _ _ _ (by simp; omega)]
    change ((compileFn c).gates ⟨N + iOffset c i + j - N, _⟩).eval ((compileFn c).wireValue input)
      = _
    simp only [show N + iOffset c i + j - N = iOffset c i + j from by omega, compileFn]
    change (compileGates c ⟨iOffset c i + j, _⟩).eval ((compileFn c).wireValue input) = _
    exact compileGate_eval_at_iOffset c i hi j hj _ _
  exact chainCollapse c input (c.gates ⟨i, hi⟩) (iOffset c i) (by unfold G'; omega)
    (by unfold G'; omega) chain_wire
    (fun p => ih_outer _ (c.acyclic ⟨i, hi⟩ p))
theorem wireValue_remapWire (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (w : Fin (N + G)) :
    (compileFn c).wireValue input (remapWire c w) = c.wireValue input w := by
  have hmain : ∀ n, (hn : n < N + G) →
      (compileFn c).wireValue input (remapWire c ⟨n, hn⟩) = c.wireValue input ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      by_cases hw : n < N
      · rw [Circuit.wireValue_lt _ _ _ (by rw [remapWire_input c _ hw]; exact hw)]
        rw [Circuit.wireValue_lt _ _ _ hw]
        congr 1; exact Fin.ext (remapWire_input c _ hw)
      · push Not at hw
        have hi : n - N < G := by omega
        -- RHS = gate eval
        have rhs_eq : c.wireValue input ⟨n, hn⟩ =
            (c.gates ⟨n - N, hi⟩).eval (c.wireValue input) := by
          rw [Circuit.wireValue_ge]; simp; omega
        rw [rhs_eq]
        -- LHS: remapWire maps to last chain wire
        rw [show ⟨n, hn⟩ = (⟨N + (n - N), by omega⟩ : Fin (N + G)) from Fin.ext (by simp; omega)]
        rw [show remapWire c ⟨N + (n - N), by omega⟩ =
            ⟨N + iOffset c (n - N) + chainLen (c.gates ⟨n - N, hi⟩).fanIn - 1, by
            have := iOffset_chain_le_iTotal c hi; have := chainLen_pos
              (c.gates ⟨n - N, hi⟩).fanIn; unfold G'; omega⟩
            from Fin.ext (by rw [remapWire_gate c hi])]
        exact lastChainValue_eq c input (n - N) hi (fun w' hw' => by
          simp_all)
  exact hmain w.val w.isLt
lemma compileGate_eval_at_oOffset (c : Circuit Basis.unboundedAON N M G)
    (j' : Nat) (hj' : j' < M) (p : Nat) (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn)
    (hidx : iTotal c + prefixSum (oChainF c) j' + p < G' c := by
      have := oOffset_chain_le_G' c hj'; unfold oOffset G' at *; omega)
    (wv : BitString (N + G' c)) :
    (compileGates c ⟨iTotal c + prefixSum (oChainF c) j' + p, hidx⟩).eval wv =
      (mkChainGate (by omega : 0 < N + G' c) (c.outputs ⟨j', hj'⟩).op (c.outputs ⟨j', hj'⟩).fanIn
        (fun i => remapWire c ((c.outputs ⟨j', hj'⟩).inputs i))
        (c.outputs ⟨j', hj'⟩).negated
        (N + oOffset c j') p hp
        (by have := oOffset_chain_le_G' c hj'; omega)).eval wv := by
  have hNotInternal : ¬(iTotal c + prefixSum (oChainF c) j' + p < iTotal c) := by omega
  have hoff : (iTotal c + prefixSum (oChainF c) j' + p) - iTotal c = prefixSum (oChainF c) j' + p
    := by omega
  have hoff_lt : prefixSum (oChainF c) j' + p < oTotal c := by
    have := oOffset_chain_le_G' c hj'; unfold G' oOffset oTotal at *; omega
  -- `compileGateInputs` looks the segment up at `idx - iTotal c`, so state the lookup at
  -- that (unreduced) index; quantifying over the bound lets `hoff` rewrite under it.
  have hSegAt : ∀ h : iTotal c + prefixSum (oChainF c) j' + p - iTotal c < oTotal c,
      segLookup M (oChainF c) (iTotal c + prefixSum (oChainF c) j' + p - iTotal c) h = (j', p) := by
    rw [hoff]
    exact fun h => oSegLookup_eq c j' hj' p hp h
  have hlt : iTotal c + prefixSum (oChainF c) j' + p - iTotal c < oTotal c := by omega
  have hSeg1 : (segLookup M (oChainF c)
      (iTotal c + prefixSum (oChainF c) j' + p - iTotal c) hlt).1 = j' := by rw [hSegAt hlt]
  have hSeg2 : (segLookup M (oChainF c)
      (iTotal c + prefixSum (oChainF c) j' + p - iTotal c) hlt).2 = p := by rw [hSegAt hlt]
  unfold compileGates
  simp only [compileGateOp, compileGateInputs, compileGateNeg, Fin.val_mk,
             dif_neg hNotInternal, mkChainGate]
  refine congrArg (fun g => Gate.eval g wv) ?_
  exact mkChainGate_gate_congr c
    (g := c.outputs ⟨(segLookup M (oChainF c)
      (iTotal c + prefixSum (oChainF c) j' + p - iTotal c) hlt).1,
      segLookup_fst_lt M _ _ hlt⟩)
    (g' := c.outputs ⟨j', hj'⟩)
    (congrArg c.outputs (Fin.ext hSeg1)) (by rw [hSeg1]) hSeg2
theorem lastOutputChainValue_eq (c : Circuit Basis.unboundedAON N M G) (input : BitString N)
    (j' : Nat) (hj' : j' < M) :
    (compileFn c).wireValue input
      ⟨N + oOffset c j' + chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1, by
        have := oOffset_chain_le_G' c hj'
        have := chainLen_pos (c.outputs ⟨j', hj'⟩).fanIn
        omega⟩ =
    (c.outputs ⟨j', hj'⟩).eval (c.wireValue input) := by
  have hle := oOffset_chain_le_G' c hj'
  have hpos := chainLen_pos (c.outputs ⟨j', hj'⟩).fanIn
  -- Reindex: N + x + y - 1 → N + x + (y - 1)
  suffices h : (compileFn c).wireValue input
      ⟨N + oOffset c j' + (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1), by omega⟩ =
      (c.outputs ⟨j', hj'⟩).eval (c.wireValue input) by
    have heq : N + oOffset c j' + chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1 =
        N + oOffset c j' + (chainLen (c.outputs ⟨j', hj'⟩).fanIn - 1) := by omega
    simp_all
  -- Each chain wire evaluates to its compiled gate
  have chain_wire : ∀ p : Nat, (hp : p < chainLen (c.outputs ⟨j', hj'⟩).fanIn) →
      (compileFn c).wireValue input ⟨N + oOffset c j' + p, by omega⟩ =
      (mkChainGate (by omega : 0 < N + G' c) (c.outputs ⟨j', hj'⟩).op (c.outputs ⟨j', hj'⟩).fanIn
        (fun i => remapWire c ((c.outputs ⟨j', hj'⟩).inputs i)) (c.outputs ⟨j', hj'⟩).negated
        (N + oOffset c j') p hp (by omega)).eval
        ((compileFn c).wireValue input) := by
    intro p hp
    rw [Circuit.wireValue_ge _ _ _ (by simp; omega)]
    change ((compileFn c).gates ⟨N + oOffset c j' + p - N, _⟩).eval
      ((compileFn c).wireValue input) = _
    simp only [show N + oOffset c j' + p - N = oOffset c j' + p from by omega, compileFn]
    have hoOff : oOffset c j' = iTotal c + prefixSum (oChainF c) j' := rfl
    change (compileGates c ⟨iTotal c + prefixSum (oChainF c) j' + p, _⟩).eval
      ((compileFn c).wireValue input) = _
    exact compileGate_eval_at_oOffset c j' hj' p hp _ _
  exact chainCollapse c input (c.outputs ⟨j', hj'⟩) (oOffset c j') (by omega)
    (by omega) chain_wire (fun p => wireValue_remapWire c input _)
theorem compile_eval (c : Circuit Basis.unboundedAON N M G) :
    (compileFn c).eval = c.eval := by
  funext input j
  -- LHS: (compileFn c).eval input j = (compileOutputs c j).eval ((compileFn c).wireValue input)
  change (compileOutputs c j).eval ((compileFn c).wireValue input) =
       (c.outputs j).eval (c.wireValue input)
  -- The output gate is a passthrough AND(lastWire, lastWire) with no negation
  simp only [compileOutputs, Gate.eval, Basis.andOr2, AONOp.eval_two_and, Bool.and_self,
             Bool.false_xor]
  -- Now we need: wireValue at the last output chain wire = original output gate eval
  exact lastOutputChainValue_eq c input j.val j.isLt
end CompileAON
instance : CompleteBasis Basis.andOr2 :=
  CompleteBasis.of_simulation Basis.unboundedAON Basis.andOr2
    fun c => ⟨CompileAON.G' c, CompileAON.compileFn c, CompileAON.compile_eval c⟩
end CircuitComplexity


