-- Prove2me | Definitions.Def_EuclidDiamStream_spaceComplexity
-- name    : EuclidDiamStream_spaceComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:12.790202+00:00
-- url     : https://prove2.me/theorems/8f5ce00a-8226-48ee-8b0d-a7d2b3687a40
-- title:
--   Space complexity $\mathcal S^+(\mathcal A,m)$ (Definition 2.3)
-- statement:
--   For $m\in\mathbb N$, $W^+(\mathcal A,m)$ is the set of final internal states that $\mathcal A$ may hold over all streams $\sigma$ with $\|\mathrm{freq}(\sigma)\|_\infty\le m$ and all settings of the randomness. The **space complexity** of $\mathcal A$ is
--   $$\mathcal S^+(\mathcal A,m)=\lceil\log_2|W^+(\mathcal A,m)|\rceil.$$
--
--   The measure counts the states reachable at the end of a stream with bounded final frequencies, however long the stream is.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ and is $\infty$ when $W^+(\mathcal A,m)$ is infinite, since the state type is arbitrary. The streams are strict-turnstile, and the seeds range over the support of the seed distribution.
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7, Def. 2.3

import Mathlib
import Definitions.Def_EuclidDiamStream_StreamAlg

namespace EuclidDiamStream

/-- The set `W⁺(A,m)` of Definition 2.3 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.7: the final internal states
the algorithm may hold over all strict-turnstile streams with `‖freq(σ)‖_∞ ≤ m` and all settings of the
randomness.

**Formalization Note.** A strict stream has a nonnegative final frequency vector, so `‖freq(σ)‖_∞ ≤ m` is
`BoolCSPDel.freq σ x ≤ m` for all `x`. There is no bound on the stream's length. "All settings of randomness" ranges
over the seeds in the support of `μ`, those the algorithm can draw. -/
def StreamAlg.reachable {U R W : Type} [Fintype R] [DecidableEq U] (A : StreamAlg U R W) (m : ℕ) :
    Set W :=
  {w | ∃ σ : List (U × Bool), BoolCSPDel.IsLegal σ ∧ (∀ x, BoolCSPDel.freq σ x ≤ m) ∧ ∃ ρ ∈ A.μ.support, w = A.toTurnstileAlg.run ρ σ}

open Classical in
/-- The space complexity `S⁺(A,m) = ⌈log₂ |W⁺(A,m)|⌉` of Definition 2.3, p.7.

**Formalization Note.** The value lies in `ℕ∞`: it is `⊤` when `W⁺(A,m)` is infinite, since the state type
is arbitrary and `Set.ncard` of an infinite set is `0`. -/
noncomputable def StreamAlg.spaceComplexity {U R W : Type} [Fintype R] [DecidableEq U]
    (A : StreamAlg U R W) (m : ℕ) : ℕ∞ :=
  if (A.reachable m).Finite then (Nat.clog 2 (A.reachable m).ncard : ℕ) else ⊤

end EuclidDiamStream


