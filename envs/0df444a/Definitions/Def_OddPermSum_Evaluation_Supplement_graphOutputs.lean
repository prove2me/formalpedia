-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_graphOutputs
-- name    : OddPermSum_Evaluation_Supplement_graphOutputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:33.353347+00:00
-- url     : https://prove2.me/theorems/9337f504-627e-4141-913b-0d6c8a6f8c1f
-- title:
--   Explicit graph outputs and joint success events
-- statement:
--   The length-and-support output is the prefix-coded integer $\ell$ followed by all $n^2$ membership bits of $E_\ell$. A cycle output is a prefix-coded closed list of vertex labels, verified against the original graph. All executions use the published bit-RAM with empty advice.
--
--   A success event requires an actual halt with the specified output within both a finite unconditional horizon $T$ and the length-sensitive time bound. Its probability is taken over the uniform $T$-bit tape; earlier halting ignores unused suffix bits. The separate predicate for the general time bound quantifies over every infinite coin stream.
--
--   Thus correctness and the faster time occur on the same event, and the output contains the full arc union or an explicit cycle, as appropriate.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorems 1.2–1.3 and following sentence; 15–16 and 22

import Definitions.Def_OddPermSum_Evaluation_Supplement_bitModel

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

noncomputable def supportOutput {n : ℕ} (D : Digraph n) (ℓ : ℕ) : List Bool := by
  classical
  exact encodeNats [ℓ] ++ ((List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => decide ((i,j) ∈ shortestArcs D ℓ))

/-- Output an explicit closed vertex sequence, in the same prefix code as natural-number arrays. -/
def cycleOutput {n : ℕ} (p : List (Fin n)) : List Bool := encodeNats (p.map Fin.val)

noncomputable def graphRun {n : ℕ} (p : BitProgram) (D : Digraph n)
    (coins : ℕ → Bool) (t : ℕ) : BitState :=
  runBits p n (directedInput D) [] coins t

/-- All tapes halt by the given number of charged machine steps. -/
noncomputable def graphHalts {n : ℕ} (p : BitProgram) (D : Digraph n) (t : ℕ) : Prop :=
  ∀ coins, (graphRun p D coins t).halted = true

/-- A successful run halts by the length-sensitive time limit and has the entire desired output.
The fair tape prefix has the unconditional worst-case length, not a success-conditioned length. -/
noncomputable def supportSuccess {n : ℕ} (p : BitProgram) (D : Digraph n) (ℓ T : ℕ) (bound : ℝ) : ℝ :=
  fairProbability T fun c => ∃ t ≤ T,
    (t : ℝ) ≤ bound ∧ (graphRun p D (extendCoins c) t).halted = true ∧
    (graphRun p D (extendCoins c) t).output = supportOutput D ℓ

noncomputable def cycleSuccess {n : ℕ} (p : BitProgram) (D : Digraph n) (ℓ T : ℕ) (bound : ℝ) : ℝ :=
  fairProbability T fun c => ∃ t ≤ T, (t : ℝ) ≤ bound ∧
    (graphRun p D (extendCoins c) t).halted = true ∧
    ∃ path, ValidCycle D ℓ path ∧ (graphRun p D (extendCoins c) t).output = cycleOutput path

end OddPermSum.Evaluation.Supplement


