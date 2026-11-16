-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Progression
-- name    : HypercliqueCircuits_Circuits_Supplement_Progression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:12:02.233045+00:00
-- url     : https://prove2.me/theorems/13fb0705-b93c-425c-bfc2-293520811f68
-- title:
--   Nontrivial arithmetic progressions and set-indicator inputs
-- statement:
--   For a set $A\subseteq\{0,\ldots,n\}$, define the presence of a nontrivial $k$-term arithmetic progression by
--
--   $$\exists a,d\in\mathbb N,\quad d\ge1\quad\text{and}\quad a+jd\in A\quad(0\le j<k).$$
--
--   Both endpoints 0 and $n$ are allowed. The input is $n$ followed by the $n+1$ indicator words of $A$ in increasing order. The specified output is the single word 1 when such a progression exists and 0 otherwise. This mathematical output specification is not a machine instruction: a program must compute it by the published scalar operational semantics.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 5 and preceding k-AP discussion (PDF 3); §4.4, p.26 (PDF 27)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Encoding

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- A nontrivial AP has positive integer step. Fin (n+1) includes BOTH
endpoints 0 and n; membership forces every term to lie in the input set.
Alman et al., Theorem 5, printed pp.2,26 / PDF pp.3,27. -/
def HasProgression {n : ℕ} (k : ℕ) (A : Finset (Fin (n + 1))) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ j : Fin k, a + j.val * d ∈ A.image Fin.val

def progressionInput {n : ℕ} (A : Finset (Fin (n + 1))) : List (Cell Empty) :=
  words (n :: (List.finRange (n + 1)).map (fun i => if i ∈ A then 1 else 0))

noncomputable def progressionOutput {n : ℕ} (k : ℕ)
    (A : Finset (Fin (n + 1))) : List (Cell Empty) := by
  classical
  exact words [if HasProgression k A then 1 else 0]

end HypercliqueCircuits.Circuits.Supplement


