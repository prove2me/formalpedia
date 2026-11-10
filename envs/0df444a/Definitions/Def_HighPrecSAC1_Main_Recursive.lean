-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Recursive
-- name    : HighPrecSAC1_Main_Recursive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:24:56.287128+00:00
-- url     : https://prove2.me/theorems/31ed167c-feb2-4305-8803-7d6ee068d3b4
-- title:
--   The recursive layer approximation of equations (3.2)–(3.5)
-- statement:
--   The local evaluator supplies lower and upper relative approximations. The module constructs C+ and C- from the ordered Jacobian products and implements the well-founded recursion for b_k(t), including the exact base case, earlier-layer accuracies, the minimum window length, evaluator accuracy, positive-part subtraction and final downward rounding. No global correctness conclusion is assumed by the oracle predicate.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 14 (PDF 15)

import Definitions.Def_HighPrecSAC1_Main_Quadratic

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

abbrev ApproxOracle (m : ℕ) := ℕ → ℕ → ℕ → Vec m → Vec m → Vec m × Vec m

noncomputable def OracleValid {m : ℕ} (O : ApproxOracle m) : Prop :=
  ∀ k t q A B, 1 ≤ q → 0 ≤ A → 0 ≤ B →
    (1-err q) • A ≤ (O k t q A B).1 ∧ (O k t q A B).1 ≤ A ∧
    B ≤ (O k t q A B).2 ∧ (O k t q A B).2 ≤ (1+err q) • B

/-- Equations (3.3) and (3.4), with the earlier recursive outputs supplied as y. -/
noncomputable def corrections {K m : ℕ} (S : LayerSystem K m) (k t : ℕ)
    (y : ℕ → Vec m) : Vec m × Vec m :=
  let len := min k ((t+1)/2+3)
  let a := k-len
  let q := fun i => (S.at i).eval (y (i-1))
  let J := fun i => (S.at i).jac (y (i-1))
  (q k + ∑ i ∈ Finset.Ico (a+1) k, (propagate J i (k-i)).mulVec (q i),
   ∑ i ∈ Finset.Ico (a+1) k, (propagate J i (k-i)).mulVec (y i))

/-- The actual well-founded recursion (3.5), parametrized only by the local evaluator. -/
noncomputable def recursiveApprox {K m : ℕ} (S : LayerSystem K m) (O : ApproxOracle m)
    (k t : ℕ) : Vec m :=
  if hk : k = 0 then S.initial else
    let y := fun i => if hi : i < k then
      recursiveApprox S O i ((t+1)/2 + 2*(k-i)) else 0
    let C := corrections S k t y
    let lu := O k t (t + min k ((t+1)/2+3) + 3) C.1 C.2
    fun v => roundDown (t+2) (posSub (lu.1 v) (lu.2 v))
termination_by k

end HighPrecSAC1.Main


