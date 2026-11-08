-- Prove2me | Definitions.Def_AsymSpecConn_IsStrassenSemiring
-- name    : AsymSpecConn_IsStrassenSemiring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:00.082449+00:00
-- url     : https://prove2.me/theorems/ca9e957f-61ec-4f9d-ab26-5bdbc879c297
-- title:
--   Strassen semiring
-- statement:
--   A **Strassen semiring** is a commutative semiring $\mathcal S$ with a preorder $\le$ such that:
--
--   1. $s\le t$ implies $s+u\le t+u$ and $su\le tu$ for all $s,t,u\in\mathcal S$;
--   2. the natural numbers, identified with their image in $\mathcal S$, carry their usual order: $m\le n$ in $\mathcal S$ if and only if $m\le n$ in $\mathbb N$;
--   3. (Archimedean) for all nonzero $s,t\in\mathcal S$ there is an integer $m\ge1$ with $s\le mt$.
--
--   This is the setting of the whole abstract theory: asymptotic spectra, $\mathcal A$-decompositions and interpolation of spectral points.
--
--   **Formalization Note** The preorder is an explicit parameter `P : Preorder S`, so one semiring may carry several preorders. This is deliberately the source's notion and not `MME.StrassenPreorder`, which also requires $1\le a$ for nonzero $a$ and an integer upper bound for every element; the source assumes $1\le s$ only in its §2.5.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §2, p.12

import Mathlib

set_option autoImplicit false

namespace AsymSpecConn

/-- **Strassen semiring** (§2, p.12 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)).

A commutative semiring `S` with a preorder `P` is a Strassen semiring if
1. `s ≤ t` implies `s + u ≤ t + u` and `s * u ≤ t * u`;
2. the natural numbers, identified with their image in `S`, carry the usual order:
   `(m : S) ≤ (n : S) ↔ m ≤ n`;
3. (Archimedean) for all nonzero `s, t` there is an integer `m ≥ 1` with `s ≤ m * t`.

**Formalization Note** The preorder is passed explicitly as `P : Preorder S`, so that the
same semiring can carry several preorders. This is the paper's (weaker) notion: it does not
require `1 ≤ s` for nonzero `s` (that is an extra assumption of §2.5 only) nor an integer
upper bound for every element, unlike `MME.StrassenPreorder`. Injectivity of `ℕ → S` follows
from clause 2. -/
def IsStrassenSemiring (S : Type*) [CommSemiring S] (P : Preorder S) : Prop :=
  (∀ s t u : S, P.le s t → P.le (s + u) (t + u)) ∧
  (∀ s t u : S, P.le s t → P.le (s * u) (t * u)) ∧
  (∀ m n : ℕ, P.le (m : S) (n : S) ↔ m ≤ n) ∧
  (∀ s t : S, s ≠ 0 → t ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ P.le s ((m : S) * t))

end AsymSpecConn


