-- Prove2me | Definitions.Def_CallCountPOPBR_IsAdmissibleRule
-- name    : CallCountPOPBR_IsAdmissibleRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:18.059921+00:00
-- url     : https://prove2.me/theorems/333a32b3-11fc-4c45-a231-e4ca896768a7
-- title:
--   Admissible periodic branching rule
-- statement:
--   A branching rule of period $p$ assigns to each phase $r\in\{0,\dots,p-1\}$ a pair of offsets $(a_r,b_r)$. It is **admissible** for window $d$ when
--   $$
--   1\le a_r\le b_r\le d\qquad(0\le r<p).
--   $$
--
--   The call at index $n\ge d$ then makes its two recursive calls at offsets $a_{n\bmod p}$ and $b_{n\bmod p}$.
--
--   **Formalization Note** The paper's unordered pair is the ordered pair with $a_r\le b_r$. The rule is a function on all natural numbers and is constrained only at phases $r<p$; it is only ever read at $n\bmod p<p$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Definition 2.1, p.4

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Admissible periodic branching rule** (Definition 2.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Definition 2.1, p.4:
"unordered pairs (a_r, b_r) for r ∈ {0, …, p − 1} … where 1 ≤ a_r ≤ b_r ≤ d".

`rule r = (a_r, b_r)` is the offset pair of phase `r`.

**Formalization Note.** The unordered pair is the ordered pair with `a_r ≤ b_r`, exactly as
printed. The rule is a function on all of `ℕ`, constrained only at phases `r < p`; the
recursion (3) reads it only at `n mod p < p`, so its values at `r ≥ p` are irrelevant. -/
def IsAdmissibleRule (d p : ℕ) (rule : ℕ → ℕ × ℕ) : Prop :=
  ∀ r, r < p → 1 ≤ (rule r).1 ∧ (rule r).1 ≤ (rule r).2 ∧ (rule r).2 ≤ d

end CallCountPOPBR


