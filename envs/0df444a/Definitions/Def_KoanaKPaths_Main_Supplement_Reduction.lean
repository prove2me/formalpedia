-- Prove2me | Definitions.Def_KoanaKPaths_Main_Supplement_Reduction
-- name    : KoanaKPaths_Main_Supplement_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:55.202595+00:00
-- url     : https://prove2.me/theorems/2ec24588-75f6-4b3c-b34f-5dc6e53ad9c0
-- title:
--   Section 4.2 — shared-gate packing compiler and machine composition
-- statement:
--   For the explicit family $E=(E_0,\ldots,E_{m-1})$, let $M_h$ be the word of the increasingly ordered elements of $E_h$. The **packing compiler** creates the shared right-skew circuit prescribed in Section 4.2, with $P_{0,0}=P_{h,0}=1$ and, using one-based stage labels,
--   $$
--   P_{h,j}=\begin{cases}P_{h-1,j}+P_{h-1,j-1}M_h,&j<h,\\ P_{h-1,h-1}M_h,&j=h,\end{cases}
--   \qquad 1\le j\le\min(h,k).
--   $$
--   Multiplication by a block appends successive right-variable gates. Previous row positions refer to shared gates; the compiler never constructs the expanded polynomial. Its output is $P_{m,k}$. The builder stores only the processed-stage count, gate list and previous-row positions. No correctness or complexity assertion is a field of this data.
--
--   The relation $\operatorname{CompilesThenRuns}(M,A,K_0,c_0)$ specifies deterministic compilation followed by a circuit machine $A$ on the same tape. Any circuit-machine execution with output $o$ and bound $B$ gives an execution of $M$ with the same output, within
--   $$
--   K_0(1+dk+L)^{c_0}+K_0\bigl(|\operatorname{natCode}(a)|+|\operatorname{natCode}(b)|\bigr)+K_0B
--   $$
--   bit steps, where $L$ is the family code length. This explicitly permits only constant slowdown of the randomized call; copying the controls is charged separately. Correctness, polynomial compilation and the final approximation bound remain assertions of Theorem 3.
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 10 (PDF p. 11), Section 4.2, proof of Theorem 3, triangular recurrence and consecutive right-product gates; composition cost uses the published finite-stack machine model

import Mathlib
import Definitions.Def_KoanaKPaths_Main_Circuits
import Definitions.Def_KoanaKPaths_Main_Supplement_Packings

open HypergraphUnreliability.FPRAS

namespace KoanaKPaths.Main.Supplement

/-- Shared gate list and the previous triangular row, storing positions of `P_{h,j}`.
This structure contains data only, with no correctness or complexity promises. -/
structure PackingBuilder where
  processed : ℕ
  gates : List Gate
  row : List ℕ

/-- Append a block by successive right-variable gates, retaining every predecessor gate. -/
def appendBlock (gates : List Gate) (pred : ℕ) (word : List ℕ) : List Gate × ℕ :=
  word.foldl (fun st u => (st.1 ++ [Gate.mulVar st.2 u], st.1.length)) (gates, pred)

/-- One row of §4.2. Row position zero always points to the existing constant-one gate.
For `j = h` only the product is used; for `j < h` an addition gate includes the omission case. -/
def packingStage (k : ℕ) (st : PackingBuilder) (S : Finset ℕ) : PackingBuilder :=
  let h := st.processed + 1
  let next := (List.range (min h k)).foldl (fun acc j0 =>
    let j := j0 + 1
    let prod := appendBlock acc.1 (st.row.getD j0 0) (blockWord S)
    if j < h then
      (prod.1 ++ [Gate.add (st.row.getD j 0) prod.2], acc.2 ++ [prod.1.length])
    else
      (prod.1, acc.2 ++ [prod.2])) (st.gates, [0])
  ⟨h, next.1, next.2⟩

/-- The compiler builds gates, never the expanded polynomial. The state `P_{0,0}=1`
is a single shared gate, also used for every `P_{h,0}`. -/
def packingCircuit (E : List (Finset ℕ)) (k : ℕ) : Circuit :=
  let st := E.foldl (packingStage k) ⟨0, [Gate.const true], [0]⟩
  ⟨st.gates, st.row.getD k 0⟩

/-- Operational meaning of deterministic compilation followed by a circuit machine on the same
unmodified fair-bit tape. Preprocessing costs a uniform polynomial in `d*k` and family bit length;
control copying is linear in its binary encoding length; the randomized call has constant slowdown.
No correctness or cost assertion is built into the instance data. -/
def CompilesThenRuns (M A : CoinMachine) (K c : ℕ) : Prop :=
  ∀ (E : List (Finset ℕ)) (d k : ℕ), ValidFamily E d k →
    ∀ (a b : ℕ) (tape out : List Bool) (B : ℕ), B < tape.length →
      A.RunsWithin (circuitCode (packingCircuit E k) ++ natCode a ++ natCode b) tape B out →
      M.RunsWithin (packingControlInput E d k a b) tape
        (K * (1 + d * k + (familyCode E).length) ^ c +
          K * ((natCode a).length + (natCode b).length) + K * B) out

end KoanaKPaths.Main.Supplement


