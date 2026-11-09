-- Prove2me | Definitions.Def_HSElemKernel_TwoLevelHash
-- name    : HSElemKernel_TwoLevelHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:00.628287+00:00
-- url     : https://prove2.me/theorems/1879ab00-aee0-4aa9-bdba-7510913de5b7
-- title:
--   Two-level hash pair $\mathcal F = (\tilde h, \mathcal H_2)$
-- statement:
--   A **two-level hash pair** $\mathcal F = (\tilde h, \mathcal H_2)$ on a finite set $W$ consists of numbers $B, q_2, t$, a first-level function
--   $$\tilde h : W \to [B]$$
--   distributing $W$ into $B$ buckets, and a family $\mathcal H_2 = \{g_1, \dots, g_t\}$ of candidate second-level functions $g_r : W \to [q_2]$ splitting each bucket into $q_2$ subbuckets. All buckets share the family; each bucket may choose a different candidate.
--
--   **Formalization Note** $[r] = \{1, \dots, r\}$ is represented 0-based. When $\mathcal F$ is used inside $\Phi_{\mathcal F}$, it is defined on the whole universe $U$ and only its values on $W = U \setminus X$ are read.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 4.1, p.8

import Mathlib

namespace HSElemKernel

/-- A pair `F = (h̃, H₂)` of two-level hashing (Sheng–Xiao, arXiv:2609.06512, held version sha256
aca9c70e…, Section 4.1, p.8): a first-level function `h̃ : W → [B]` into `B` buckets and `t`
candidate second-level functions `g₁, …, g_t : W → [q₂]`.

**Formalization Note** `[r] = {1, …, r}` is `Fin r` (0-based). The element type `α` is the
hashed set `W`; when `F` is used inside `Φ_F` it is the whole universe `Fin n` and only the values
on `W = U \ X` are ever read. -/
structure TwoLevelHash (α : Type) where
  /-- the number `B` of first-level buckets -/
  B : ℕ
  /-- the number `q₂` of subbuckets per bucket -/
  q2 : ℕ
  /-- the number `t` of candidate second-level functions -/
  t : ℕ
  /-- the first-level function `h̃` -/
  h : α → Fin B
  /-- the candidates `g_r`, `r ∈ [t]` -/
  g : Fin t → α → Fin q2

end HSElemKernel


