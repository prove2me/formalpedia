-- Prove2me | Definitions.Def_DetDLP_W3_Driver
-- name    : DetDLP_W3_Driver
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T21:10:32.791298+00:00
-- url     : https://prove2.me/theorems/24bb84e6-05c0-4ad4-ae8e-aefbeb5dcf5f
-- title:
--   Stage II driver: certified subroutine calls and branch outputs
-- statement:
--   A large-regime output carries a native factor base, an inclusion of Stage I tuple image in its tuple image, valid coordinate decompositions, and an actual bounded HNF trace. A small-regime output is the found index in a scan of the canonical exponent range. The machine-level interface shares packet encodings between the terminal builder and contraction and uses the exact HNF operation on all consistent rows.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, proof of Theorem 1.1 and Lemma 4.4, pp. 13–16; revision R1.

import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
namespace DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The common large-group guard. In the multiplicative case equality at the one-element
    difference between this guard and the native-query guard is safe in the table scan. -/
def w3_large (p M : ℕ) : Prop := 67 < p ∧ 64 ≤ M ∧ 4096 * blockCount (bitLen p) ≤ M-1

/-- The lookup builder and contraction subroutines, including their shared packet. -/
def w3_terminalOps (fam : w3_Query → Prop) : Prop :=
  ∃ (C c : ℕ) (build : PrimitiveMachine) (ob : Fin build.tapeCount)
    (eval : PrimitiveMachine) (oe : Fin eval.tapeCount)
    (contract : PrimitiveMachine) (oc : Fin contract.tapeCount) (K : ℕ),
    0 < C ∧ 0 < c ∧ ∀ q, fam q → ∃ n : w3_Net q C,
      RunsWithin build ob q.input (w3_packet n) (polyBound c q.input.length) (polyBound c q.input.length) ∧
      BTNEntryEvaluable n.desc n.G (w3_precision q) (w3_len q) n.T eval oe
        (polyBound c (n.S+n.desc.length)) (polyBound c (n.S+n.desc.length)) ∧
      ∃ w, EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T) ∧
        RunsWithin contract oc (w3_packet n) w
          (polyBound K (n.S+n.desc.length)*mainTimeBound K q.b) (polyBound K (n.S+n.desc.length))

/-- The projection of Lemma 4.4 used by the dispatcher. The conditional bound applies to
    violated rows, while consistency suffices for an exact update. -/
def w3_hnfOps : Prop := ∃ (machine : PrimitiveMachine) (out : Fin machine.tapeCount) (K : ℕ),
  ∀ (M N : ℕ) [NeZero M], 2 ≤ M → 1 ≤ N → ∀ (s : w3_Rep M N) (r : w3_Row M N),
    IsModularLatticeBasis M s.2 → (∃ z ∈ w3_coset s, w3_holds r z) →
    ∃ t, w3_update r s t ∧ (¬ w3_holds r s.1 → 2 * Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) ∧
      RunsWithin machine out
        (encodeCosetUpdateInput M (fun i => (s.1 i).val) s.2 (fun i => (r.1 i).val) r.2.val)
        (encodeCosetRep (fun i => (t.1 i).val) t.2) (polyBound K (N + bitLen M)) (polyBound K (N + bitLen M))

/-- The list and subroutine certificates of the elliptic projection of Theorem 3.1. -/
def w3_ecBaseCalls (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine)
    (do' : Fin de.tapeCount) (K : ℕ) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (F : Fin (blockCount (bitLen p)) → List E.toAffine.Point) : Prop :=
  letI := ecPointFintype E
  let b := bitLen p
  let m := blockCount b
  let M := Fintype.card E.toAffine.Point
  (∀ i, (F i).Nodup) ∧
    ((∑ i, (F i).length : ℕ) : ℝ) ≤ (K : ℝ)*((m : ℝ)^2+(m : ℝ)*(M : ℝ)^((1 : ℝ)/(m : ℝ))) ∧
    7*M ≤ 8*(sumsetAdd fun i => (F i).toFinset).card ∧
    RunsWithin en eo (encodeCurveInput p E) (encodeECFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) ∧
    ∀ X : E.toAffine.Point, ∃ A B : Fin m → E.toAffine.Point,
      (∀ i, A i ∈ F i ∧ B i ∈ F i) ∧ (∑ i, (A i+B i)) = X ∧
      RunsWithin de do' (Encoding.encodeList id [encodeCurveInput p E,encodeNatListBin (pointCoords X)])
        (encodeECDecomp A B) (mainSpaceBound K b) (polyBound K b)

/-- The list and subroutine certificates of the multiplicative projection of Theorem 3.1. -/
def w3_fpBaseCalls (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine)
    (do' : Fin de.tapeCount) (K : ℕ) {p : ℕ} [Fact p.Prime]
    (F : Fin (blockCount (bitLen p)) → List (ZMod p)ˣ) : Prop :=
  let b := bitLen p
  let m := blockCount b
  let M := p-1
  (∀ i, (F i).Nodup) ∧
    ((∑ i, (F i).length : ℕ) : ℝ) ≤ (K : ℝ)*((m : ℝ)^2+(m : ℝ)*(M : ℝ)^((1 : ℝ)/(m : ℝ))) ∧
    7*M ≤ 8*(prodsetMul fun i => (F i).toFinset).card ∧
    RunsWithin en eo (countWord p) (encodeFpFactorBlocks F) (mainSpaceBound K b) (mainSpaceBound K b) ∧
    ∀ X : (ZMod p)ˣ, ∃ A B : Fin m → (ZMod p)ˣ,
      (∀ i, A i ∈ F i ∧ B i ∈ F i) ∧ (∏ i, (A i*B i)) = X ∧
      RunsWithin de do' (encodeNatListBin [p,(X : ZMod p).val]) (encodeFpDecomp A B)
        (mainSpaceBound K b) (polyBound K b)

/-- The certificate the driver returns in the large-group regime. `ref` is the Stage I
    list and `native` is the seed-indexed list actually used by the separator. Range inclusion
    transfers universal decomposition and is reflexive when the two lists coincide. -/
def w3_traceOutput {V : Type} [AddCommGroup V] {m : ℕ} (ref native : IndexedFactorBase V m)
    (M : ℕ) [NeZero M] (P Q : V) (accepts : ℕ → Prop) : Prop :=
  Set.range ref.tupleVal ⊆ Set.range native.tupleVal ∧
    ∃ (U : Fin native.totalCoords → native.BlockTuple) (y : w3_Label M native.totalCoords),
      (∀ j, native.tupleVal (U j) = native.elem P Q j) ∧ w3_Outcome native M P U y ∧
      accepts (y native.targetCoord).val

/-- The certificate for a bounded linear scan of all canonical exponents. -/
def w3_scanOutput {V : Type} [AddMonoid V] [DecidableEq V]
    (M : ℕ) (P Q : V) (accepts : ℕ → Prop) : Prop :=
  ∃ u, (List.range M).find? (fun j => decide (j • P = Q)) = some u ∧ accepts u

end DetDLP


