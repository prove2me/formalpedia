-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_DecSpec
-- name    : CallCountPOPBR_Supplement_DecSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:01:53.987531+00:00
-- url     : https://prove2.me/theorems/95184889-4973-412c-924d-2a65b0dcb398
-- title:
--   Abstract decreasing-argument recursive specifications
-- statement:
--   An **abstract decreasing-argument recursive specification** assigns to every $n\in\mathbb N$ a finite ordered list of immediate calls $R(k)$, each with $k<n$. The list may repeat an argument, and no computability or branching bound is imposed.
--
--   The associated invocation count includes the root and is defined recursively by
--
--   $$
--   c_n=1+\sum_{k\text{ in the call list at }n}c_k.
--   $$
--
--   Since no natural number is below zero, $R(0)$ is automatically a base case.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Section 5.1, p.9

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **An abstract decreasing-argument recursive specification** (§5.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §5.1, p.9:
"Consider the model in which R(0) is a base case and each invocation R(n) may call R(k) only for
k < n. A rule may make repeated calls to the same k."

`calls n` is the list of immediate calls `R(k)` made by `R(n)` (repetitions allowed); every called
argument is smaller than `n`.

**Formalization Note.** `calls 0 = []` (R(0) is a base case) follows from `dec`. No bound is placed
on the number of calls (unrestricted branching); bounded branching is the extra condition
`(calls n).length ≤ b`. The specification is an arbitrary function, not necessarily computable
(the paper's "abstract" specification); effectivity is the extra condition `Computable calls`. -/
structure DecSpec where
  /-- The immediate calls made by `R(n)`. -/
  calls : ℕ → List ℕ
  /-- Every call is to a strictly smaller argument. -/
  dec : ∀ n, ∀ k ∈ calls n, k < n

/-- **The call count `c_n` of a specification** (§5, p.9: "c_n = |V(T_n)|", the number of
invocations on input `n`, root counted): `c_n = 1 + ∑_{k ∈ calls n} c_k`. -/
def DecSpec.count (s : DecSpec) (n : ℕ) : ℕ :=
  1 + ((s.calls n).attach.map (fun k => s.count k.1)).sum
termination_by n
decreasing_by exact s.dec n k.1 k.2

end CallCountPOPBR.Supplement


