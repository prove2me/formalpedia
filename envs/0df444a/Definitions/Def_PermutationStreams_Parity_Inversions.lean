-- Prove2me | Definitions.Def_PermutationStreams_Parity_Inversions
-- name    : PermutationStreams_Parity_Inversions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:25.46524+00:00
-- url     : https://prove2.me/theorems/36db31d9-a11d-4775-89c9-86fe8f2370d5
-- title:
--   Inversion count and sign of a finite sequence
-- statement:
--   For a finite sequence $v=(v_1,\dots,v_k)$ of elements of a linearly ordered set, the **inversion count** is the number of position pairs in the wrong order,
--
--   $$
--   \operatorname{inv}(v)=\bigl|\{(i,j): i<j,\ v_i>v_j\}\bigr|,
--   $$
--
--   and its **sign** is $\operatorname{sgn}(v)=(-1)^{\operatorname{inv}(v)}\in\{-1,+1\}$. For a permutation $\pi$ of $[n]=\{1,\dots,n\}$, read as the sequence $\pi_1,\dots,\pi_n$, this is the sign $\operatorname{sgn}(\pi)=(-1)^{\operatorname{inv}(\pi)}$ of the paper.
--
--   These two quantities are the objects every statement of the mission is about: the streaming problem asks for $\operatorname{sgn}(\pi)$, and the reduction identifies the inversion count of a block-structured permutation.
--
--   **Formalization Note** Positions are $0$-based (`Fin k`), and a permutation of $[n]$ is an `Equiv.Perm (Fin n)`, i.e. values are shifted to $\{0,\dots,n-1\}$; the shift preserves every comparison, hence the inversion count. The sign is a unit of $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: an order-preserving shift by one changes no inversion
--   - encoding: sgn(π) = (−1)^inv(π) ∈ {−1, 1} → (−1)^inv as a unit of ℤ; reason: same value
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), p. 2 (definition of inv and sgn) and §3, p. 5 (notation [n], S_n)

import Mathlib

namespace PermutationStreams.Parity

/-- Braverman–Zamir §1 p.2 and §3 p.5: the inversion count of a finite sequence
`v₀, …, v_{k-1}` in a linear order, the number of position pairs `i < j` with `v_i > v_j`.
Positions are 0-based (`Fin k`); only the relative order of the values matters. -/
def inv {α : Type} [LinearOrder α] {k : ℕ} (v : Fin k → α) : ℕ :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter (fun q => q.1 < q.2 ∧ v q.2 < v q.1)).card

/-- The sign `(-1)^{inv(v)}` of a finite sequence, as a unit of `ℤ` (that is, `±1`). -/
def sgnSeq {α : Type} [LinearOrder α] {k : ℕ} (v : Fin k → α) : ℤˣ :=
  (-1) ^ inv v

/-- p.2: `sgn(π) = (-1)^{inv(π)}` for a permutation `π` of `[n]`, read as the sequence
`π(0), …, π(n-1)` (the 0-based encoding shifts positions and values by one, which preserves
every comparison). -/
def sgn {n : ℕ} (π : Equiv.Perm (Fin n)) : ℤˣ :=
  sgnSeq (⇑π)

end PermutationStreams.Parity


