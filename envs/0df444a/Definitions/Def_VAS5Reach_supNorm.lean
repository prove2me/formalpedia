-- Prove2me | Definitions.Def_VAS5Reach_supNorm
-- name    : VAS5Reach_supNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:38.678559+00:00
-- url     : https://prove2.me/theorems/9d2b8f50-6c7a-4829-af28-e0c576a5f4b4
-- title:
--   Max norm $\|x\|$ of an integer vector
-- statement:
--   For a vector $x \in \mathbb Z^d$ the **max norm** is
--   $$
--   \|x\| := \max_{i \in [d]} |x(i)| ,
--   $$
--   with value $0$ when $d = 0$. The companion `supNormN` is the same norm for vectors of $\mathbb N^d$ (counter vectors of configurations). All sizes and bounds of the mission are stated with this norm.
--
--   **Formalization Note** Coordinates form an arbitrary finite type $\iota$ with $d = |\iota|$; the norm is a natural number.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 Preliminaries, p.13 (PDF p.15)

import Mathlib

namespace VAS5Reach

/-- The max norm `‖x‖ := max_{i∈[d]} |x(i)|` of an integer vector `x ∈ ℤ^ι`, as a natural number
(`0` when `ι` is empty).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 Preliminaries, printed
p. 13 (PDF p. 15): "We use ∥x∥ := max_{i∈[d]} |x(i)| for the max norm of x".

**Formalization Note** The coordinates form an arbitrary finite type `ι` (the paper's `[d]`, with
`d = Fintype.card ι`). The norm is valued in `ℕ` since all vectors of the paper's statements are
integral. -/
def supNorm {ι : Type} [Fintype ι] (x : ι → ℤ) : ℕ :=
  Finset.univ.sup fun i => (x i).natAbs

/-- The max norm `‖x‖ := max_i x(i)` of a natural-number vector (a configuration's counter vector),
`0` when `ι` is empty. It agrees with `supNorm` of the cast vector. -/
def supNormN {ι : Type} [Fintype ι] (x : ι → ℕ) : ℕ :=
  Finset.univ.sup x

end VAS5Reach


