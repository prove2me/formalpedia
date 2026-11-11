-- Prove2me | Definitions.Def_DigraphDFSStream_Main_DFSStreamingTarget
-- name    : DigraphDFSStream_Main_DFSStreamingTarget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:08.702192+00:00
-- url     : https://prove2.me/theorems/e6f7ab20-9a17-402b-ae33-990394881646
-- title:
--   DFS output buffers and high-probability streaming correctness
-- statement:
--   An output buffer lists directed forest edges, with each endpoint encoded in $\lfloor\log_2(n+1)\rfloor+1$ little-endian bits. Edge order is arbitrary and each forest edge is listed once. The public vertex set $[n]$ records all vertices, including isolated ones.
--
--   For a fixed input stream $\sigma$, success means that one finite halting execution returns a buffer encoding a DFS forest of the adjacency set represented by $\sigma$. Its probability is taken over the independent fair coin tape for that same execution.
--
--   For an integer confidence parameter $c\ge0$, the requested success probability is
--   $$\Pr(\text{success})\ge 1-n^{-(c+1)}\qquad(n\ge2).$$
--   Sizes zero and one require probability one. Rounding a requested positive real confidence exponent up to an integer recovers every fixed inverse-polynomial failure guarantee.
--
--   This definition connects the output semantics to the charged machine without assuming a favorable event, an implementation contract, or a correctness oracle.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Theorem 1.1 and §2, printed pp.2,4 (PDF pp.3,5)

import Definitions.Def_DigraphDFSStream_Main_GraphSemantics
import Definitions.Def_DigraphDFSStream_Main_StreamingMachine

set_option autoImplicit false

namespace DigraphDFSStream.Main

/-- Each output edge uses two fixed-width little-endian labels. The order of forest edges is free.
The buffer contains edges only; the public vertex count supplies all isolated vertices. -/
def forestBuffer {n : ℕ} (L : List (Fin n × Fin n)) : List Bool :=
  L.flatMap (fun e =>
    List.ofFn (fun i : Fin (Nat.log2 (n + 1) + 1) => Nat.testBit e.1.val i.val) ++
    List.ofFn (fun i : Fin (Nat.log2 (n + 1) + 1) => Nat.testBit e.2.val i.val))

def EncodesDFS {n : ℕ} (input : List (Fin n × Fin n)) (output : List Bool) : Prop :=
  ∃ L : List (Fin n × Fin n), L.Nodup ∧ output = forestBuffer L ∧
    IsDFSForest input.toFinset Finset.univ L.toFinset

def DFSSuccess {n : ℕ} (P : StreamProgram) (input : List (Fin n × Fin n)) :
    Set (ℕ → Bool) :=
  {ω | ∃ output, StreamHalts P input ω output ∧ EncodesDFS input output}

/-- Integer confidence exponents suffice for every fixed positive real exponent by rounding up.
The two smallest sizes require exact success, including the empty DFS forest. -/
def DFSHighProbability (P : StreamProgram) (c : ℕ) : Prop :=
  ∀ (n : ℕ) (input : List (Fin n × Fin n)),
    MeasurableSet (DFSSuccess P input) ∧
      (if n < 2 then 1 else 1 - (n : ℝ) ^ (-(c + 1 : ℝ))) ≤
        fairCoins.real (DFSSuccess P input)

end DigraphDFSStream.Main


