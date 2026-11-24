-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Supplement_Threshold
-- name    : OverflowBinPacking_IID_Supplement_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:52:18.423778+00:00
-- url     : https://prove2.me/theorems/a9707d3f-2648-4688-bdb4-9eb6e06af752
-- title:
--   Threshold rules and the one-active-bin comparison class
-- statement:
--   A one-active-bin policy never returns to a bin after assigning any item to a different bin. This is independent of bin labels. Given $\alpha\in[0,1]$, the threshold rule uses the most recently used bin while its load is at most $\alpha$ and otherwise opens a fresh bin at the next arrival:
--   $$\text{keep the current bin iff its previous load is }\le\alpha.$$
--   The same rule is defined at every horizon. Finite nonnegative support permits mass at zero and arbitrary sizes above one; strict overflow is unchanged. The policy family supplies the uniform-in-horizon object needed by Theorem C.1.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, pp. 44–47, Appendix C

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- Once a bin is left it is never reactivated; labels need not be in index order. -/
def OneActive {n : ℕ} (a : Rule n) : Prop :=
  ∀ x (i j k : Fin n), i ≤ j → j ≤ k → a i x = a k x → a j x = a i x

/-- Reuse the last bin at load ≤α; otherwise the current round's index is fresh. -/
noncomputable def thresholdChoice {n : ℕ} (α : ℝ) (x : Fin n → ℝ)
    (p : List (Fin n)) (i : Fin n) : Fin n :=
  match p.getLast? with
  | none => i
  | some j => if usage (fun k _ => (p[k.val]?).getD k) x j i ≤ α then j else i

noncomputable def thresholdPrefix {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℕ → List (Fin n)
  | 0 => []
  | t + 1 =>
    let p := thresholdPrefix α x t
    if h : t < n then p ++ [thresholdChoice α x p ⟨t, h⟩] else p

noncomputable def thresholdRule {n : ℕ} (α : ℝ) : Rule n :=
  fun i x => ((thresholdPrefix α x (i.val + 1))[i.val]?).getD i

/-- Finite support includes zero and arbitrary values larger than one. -/
def FiniteNonnegativeLaw (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ S : Finset ℝ, (∀ x ∈ S, 0 ≤ x) ∧ ν (↑S)ᶜ = 0

end OverflowBinPacking.IID.Supplement


