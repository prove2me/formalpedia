-- Prove2me | Definitions.Def_TranspositionIID_Main_Exclusion
-- name    : TranspositionIID_Main_Exclusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:06.582859+00:00
-- url     : https://prove2.me/theorems/121334d2-58db-4f00-9f19-c775a9a1b149
-- title:
--   Biased binary exclusion update and inversion count
-- statement:
--   Write binary words of length $N$ with letters $L,H$. An update chooses uniformly one of the $N-1$ adjacent pairs. Equal letters stay fixed. Unlike letters are resampled to $HL$ with probability $(1+e^{-\theta})^{-1}$ and $LH$ otherwise. Define
--   $$V(w)=\#\{(i,j):i<j,\ w_i=L,\ w_j=H\}.$$
--   The kernel is defined on all binary words and preserves every fixed-count class exactly. The milestone restricts the initial word to have at least one letter of each kind; its entire trajectory is therefore in precisely the source's fixed positive-count state space. `false` represents $L$, `true` represents $H$.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). Definition 3.1 and Lemma 3.2, printed p.5 = PDF p.5

import Definitions.Def_TranspositionIID_Main_FiniteChain

noncomputable section

namespace TranspositionIID.Main

/-- Binary words: false is L, true is H. The kernel preserves each fixed-count class. -/
abbrev BinaryWord (N : ℕ) := Fin N → Bool

/-- Number of L-before-H pairs (Definition 3.1 and Lemma 3.2, p.5). -/
def binaryInversions {N : ℕ} (w : BinaryWord N) : ℝ :=
  ((Finset.univ.filter (fun ij : Fin N × Fin N =>
    ij.1 < ij.2 ∧ w ij.1 = false ∧ w ij.2 = true)).card : ℝ)

/-- Count-preserving adjacent resampling to HL or LH. -/
def exclusionUpdate {N : ℕ} (w : BinaryWord N) (k : Fin (N - 1)) (highFirst : Bool) : BinaryWord N :=
  let a : Fin N := ⟨k.val, by omega⟩
  let b : Fin N := ⟨k.val + 1, by omega⟩
  if w a = w b then w else fun i => if i = a then highFirst else if i = b then !highFirst else w i

/-- Uniform adjacent-pair choice, followed by the exact heat-bath probabilities. -/
def exclusionKernel (N : ℕ) (θ : ℝ) : Matrix (BinaryWord N) (BinaryWord N) ℝ :=
  fun w z => ∑ k : Fin (N - 1),
    ((if exclusionUpdate w k true = z then 1 / (1 + Real.exp (-θ)) else 0) +
     (if exclusionUpdate w k false = z then 1 - 1 / (1 + Real.exp (-θ)) else 0)) /
      ((N - 1 : ℕ) : ℝ)

end TranspositionIID.Main


