-- Prove2me | Definitions.Def_AlmostMMS_bp
-- name    : AlmostMMS_bp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:40.785721+00:00
-- url     : https://prove2.me/theorems/109a6651-7dac-4c21-94f5-26bb89b15927
-- title:
--   Definition 2.3, p.12 — the breakpoint $m_i(\alpha)$
-- statement:
--   For an agent $i$ and a demand $\alpha$, the **breakpoint** $m_i(\alpha)$ is the number of items worth at least $\alpha$ to agent $i$. When the values of $i$ are non-increasing these items are exactly $e_1,\dots,e_{m_i(\alpha)}$, so agent $i$ can satisfy $\alpha$ only within that prefix. A demand that no item satisfies has breakpoint $0$.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 2.3, p.12

import Mathlib

namespace AlmostMMS

open Finset

open Classical in
/-- **Breakpoint** `m_i(α)` (Definition 2.3, p.12): the number of items worth at least `α` to agent `i`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** When the values of agent `i` are non-increasing these items form the prefix
`e₁, …, e_{m_i(α)}`. A demand that no item satisfies has breakpoint `0`. -/
noncomputable def bp {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (α : ℝ) : ℕ :=
  (univ.filter fun e => α ≤ v i e).card

end AlmostMMS


