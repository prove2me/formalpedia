-- Prove2me | Definitions.Def_PermutationStreams_Parity_Supplement_Patterns
-- name    : PermutationStreams_Parity_Supplement_Patterns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:53:57.996978+00:00
-- url     : https://prove2.me/theorems/26a2814e-e99b-442d-91cc-fc26a4fedfba
-- title:
--   Pattern detection, monotone patterns, the patterns 312 and 231, and $S_\sigma(n)$
-- statement:
--   Pattern containment and avoidance are the published notions: a permutation $\pi\in S_n$ **contains** $\sigma\in S_k$ if some positions $a_1<\dots<a_k$ carry values $\pi_{a_1},\dots,\pi_{a_k}$ order-isomorphic to $\sigma$, and **avoids** $\sigma$ otherwise.
--
--   1. A pattern $\sigma\in S_k$ is **monotone** if it is the identity $i\mapsto i$ or the reversal $i\mapsto k+1-i$.
--   2. $312$ and $231$ are the patterns of $S_3$ in one-line notation $(3,1,2)$ and $(2,3,1)$.
--   3. A one-pass algorithm with Boolean output **detects** $\sigma$ in permutations of $[n]$ if on every $\pi\in S_n$ it answers *true* exactly when $\pi$ contains $\sigma$. Nothing is required on inputs that are not permutations (the promise).
--   4. $S_\sigma(n)$ is the minimum number of bits of a deterministic one-pass algorithm that detects $\sigma$ in permutations of $[n]$:
--
--   $$
--   S_\sigma(n)=\min\{s\in\mathbb N:\ \exists\ \text{a detecting algorithm with at most }2^s\text{ states}\}.
--   $$
--
--   These are the objects of the paper's dichotomy theorem for fixed patterns.
--
--   **Formalization Note** $S_\sigma(n)$ is an `sInf` over ℕ. The set is nonempty (an automaton remembering the whole prefix detects $\sigma$); if it were empty the value $0$ would only falsify lower bounds, so no statement becomes vacuously true. Permutations are `Equiv.Perm (Fin k)`; the reversal is `Fin.revPerm`.
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §1.2 p. 2 (S_σ(n)), §3 p. 5 (order-isomorphism, containment, avoidance, monotone patterns), §5 p. 9 (patterns 312, 231)

import Definitions.Def_PermutationStreams_Parity_Supplement_OnePass
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm

namespace PermutationStreams.Parity.Supplement

open PatternRangeCounting1593.RangeCounting

/-- §3 p.5: a pattern `σ ∈ S_k` is monotone if it is increasing (the identity of `[k]`) or
decreasing (`i ↦ k + 1 - i`, which is `Fin.revPerm` in the 0-based encoding). -/
def IsMonotonePattern {k : ℕ} (σ : Equiv.Perm (Fin k)) : Prop :=
  σ = 1 ∨ σ = Fin.revPerm

/-- The pattern `312` (one-line notation `σ₁ = 3, σ₂ = 1, σ₃ = 2`), 0-based: `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`. -/
def pat312 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

/-- The pattern `231` (one-line notation `σ₁ = 2, σ₂ = 3, σ₃ = 1`), 0-based: `0 ↦ 1, 1 ↦ 2, 2 ↦ 0`. -/
def pat231 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- §1.2 p.2: a one-pass algorithm with Boolean output detects `σ` in permutations of `[n]` if on
every permutation `π` of `[n]` it answers `true` exactly when `π` contains `σ`. Inputs that are not
permutations (the promise) impose no requirement. -/
def OnePassAlg.Detects {n k : ℕ} {S : Type} (A : OnePassAlg n S Bool)
    (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ π : Equiv.Perm (Fin n), A.run π = true ↔ Contains σ π

/-- §1.2 p.2: `S_σ(n)`, the minimum number of bits used by a deterministic one-pass algorithm that
detects `σ` in permutations of `[n]`: the least `s` such that some detecting algorithm has at most
`2^s` states. (The set is nonempty for every `n`; were it empty, the value `0` would only make
lower bounds on `S_σ(n)` false, never true.) -/
noncomputable def spaceComplexity {k : ℕ} (σ : Equiv.Perm (Fin k)) (n : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ (S : Type) (_ : Fintype S) (A : OnePassAlg n S Bool),
    A.Detects σ ∧ A.UsesBits s}

end PermutationStreams.Parity.Supplement


