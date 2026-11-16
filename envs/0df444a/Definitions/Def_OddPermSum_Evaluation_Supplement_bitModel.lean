-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_bitModel
-- name    : OddPermSum_Evaluation_Supplement_bitModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:47.833137+00:00
-- url     : https://prove2.me/theorems/05a60b07-6b3a-495e-bd0b-f7239934985b
-- title:
--   Charged randomized machine interface and prefix encodings
-- statement:
--   The published bit-RAM has one finite program, bounded address words of $q(\lfloor\log_2(n+2)\rfloor+1)$ bits for a fixed program parameter $q$, bit memory, and one charged step for every instruction. Its only operations are word bookkeeping, bit Boolean operations, load/store/input, fair coins, output, jumps, and halt. Advice is empty throughout this supplement. Finite fields, irreducible-polynomial construction, algebraic evaluation and matrix multiplication must all be implemented by these instructions.
--
--   The input is unary $n$, a delimiter, and the directed adjacency bits in row-major order. Natural-number outputs use a prefix code consisting of a unary bit length, a delimiter and binary digits. A length-$T$ fair tape has the exact uniform law on $\{0,1\}^T$:
--   $$\Pr(E)=|E|/2^T.$$
--   No infinite mass is converted to a finite real. Positive logarithmic factors use $(\log_2(n+1)+1)^k$.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, time convention; 5, finite-field arithmetic; 13, graph input

import Definitions.Def_OddPermSum_Evaluation_Supplement_digraph
import Definitions.Def_MaoLowDegree_Counterexample_bitRAM

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

abbrev BitProgram := MaoLowDegree.Counterexample.BitProgram
abbrev BitState := MaoLowDegree.Counterexample.BitState
abbrev runBits := MaoLowDegree.Counterexample.runBits
abbrev extendCoins {t : ℕ} (c : Fin t → Bool) := MaoLowDegree.Counterexample.extendCoins c

/-- Prefix code: unary bit length, delimiter, then little-endian binary digits. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeNats (xs : List ℕ) : List Bool :=
  encodeNat xs.length ++ xs.flatMap encodeNat

/-- An input adjacency matrix preceded by unary n and its delimiter. -/
noncomputable def directedInput {n : ℕ} (D : Digraph n) : List Bool := by
  classical
  exact List.replicate n true ++ [false] ++
    ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => decide ((i,j) ∈ D.arcs))

/-- Uniform finite fair tape; all programs below halt within the sampled prefix. -/
noncomputable def fairProbability (t : ℕ) (E : (Fin t → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / (2 : ℝ)^t

/-- Log factors are positive, even at n=0. -/
noncomputable def logFactor (n : ℕ) (k : ℕ) : ℝ :=
  (Real.logb 2 (n+1) + 1)^k

end OddPermSum.Evaluation.Supplement


