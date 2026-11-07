-- Prove2me | Definitions.Def_LosslessQLTC_Greedy
-- name    : LosslessQLTC_Greedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:47.900821+00:00
-- url     : https://prove2.me/theorems/ca229aa5-cb9b-4029-9668-0f1a3dc9595d
-- title:
--   One iteration and runs of Algorithm 1 (greedy flipping)
-- statement:
--   **Algorithm 1** takes $f\in C^i(X)$, $1\le i\le k$. While there exist $v\in V_0$ and $h\in C^{i-2}(\mathrm{Lk}(v))$ with $\|f+\delta(\iota_vh)\|<\|f\|$, it replaces $f$ by $f+\delta(\iota_vh)$, and at the end it returns $f$. The algorithm reduces a word to a locally minimal one, which is how Theorem 4.10 reaches arbitrary words.
--
--   **Formalization Note.** The algorithm is nondeterministic, so one iteration is a relation and a run is an inductive chain of iterations with a counted length. The input level is $i=q+1$, and $h$ sits at link index $j=q$.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Algorithm 1, p.41

import Mathlib
import Definitions.Def_LosslessQLTC_Link

namespace LosslessQLTC

variable {k : ℕ}

/-- One iteration of Algorithm 1 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.41) on
`f ∈ C^i(X)`, `i = q + 1`: for some `v ∈ V_0` and `h ∈ C^{i−2}(Lk(v))` with
`∥f + δ(ι_v h)∥ < ∥f∥`, replace `f` by `f + δ(ι_v h)`. Here `h` lies at link index `j = i − 1 = q`.
The algorithm is nondeterministic in the choice of `v` and `h`. -/
def GreedyStep (X : SquareComplex k) (q : ℕ) (f g : Level X (q + 1) → ZMod 2) : Prop :=
  ∃ (v : X.Vtx) (h : LinkCochain X v q), X.type v = ∅ ∧
    g = f + delta X q (iota X v h q) ∧ normC X g < normC X f

/-- `GreedyRun X q n f g`: a run of Algorithm 1 from `f` reaches `g` in exactly `n` iterations. -/
inductive GreedyRun (X : SquareComplex k) (q : ℕ) :
    ℕ → (Level X (q + 1) → ZMod 2) → (Level X (q + 1) → ZMod 2) → Prop
  | refl (f) : GreedyRun X q 0 f f
  | step {n f g g'} : GreedyRun X q n f g → GreedyStep X q g g' → GreedyRun X q (n + 1) f g'

end LosslessQLTC


