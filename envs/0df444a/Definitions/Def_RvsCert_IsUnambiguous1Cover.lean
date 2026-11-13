-- Prove2me | Definitions.Def_RvsCert_IsUnambiguous1Cover
-- name    : RvsCert_IsUnambiguous1Cover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:06.172972+00:00
-- url     : https://prove2.me/theorems/6e6eebec-dce4-48ef-a5c2-b85fb1958126
-- title:
--   Unambiguous collection of 1-certificates
-- statement:
--   A **partial assignment** $\rho$ on the bit positions $\iota$ fixes some bits to values and leaves the others free; an input $x$ is consistent with $\rho$ if it agrees with $\rho$ on every fixed bit. A finite family $P$ of partial assignments is an **unambiguous collection of 1-certificates** for $f$ if
--
--   1. every input consistent with some $\rho\in P$ is a 1-input of $f$, and
--   2. every 1-input of $f$ is consistent with exactly one $\rho\in P$.
--
--   Such families define the unambiguous certificate complexity $\mathrm{UC}_1(f)$ used in Lemma 2.
--
--   **Formalization Note** A partial assignment is a map $\iota\to$ `Option Bool`, with `none` for a free bit.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 2, p.2 (standard notion)

import Mathlib

namespace RvsCert

/-- **Unambiguous collection of 1-certificates** (standard; used for `UC1(f)` in Lemma 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1). A finite family `P` of partial assignments `ρ : ι → Option Bool`
(`ρ i = some b` fixes bit `i` to `b`, `none` leaves it free) such that
(1) every input consistent with a member of `P` is a 1-input of `f`, and
(2) every 1-input of `f` is consistent with exactly one member of `P`. -/
def IsUnambiguous1Cover {ι : Type} (f : (ι → Bool) → Bool) (P : Finset (ι → Option Bool)) :
    Prop :=
  (∀ ρ ∈ P, ∀ x : ι → Bool, (∀ i b, ρ i = some b → x i = b) → f x = true) ∧
  (∀ x : ι → Bool, f x = true → ∃! ρ, ρ ∈ P ∧ ∀ i b, ρ i = some b → x i = b)

end RvsCert


