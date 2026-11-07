-- Prove2me | Definitions.Def_LaconicBarrier_LaconicArg_source
-- name    : LaconicBarrier_LaconicArg_source
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:16.934996+00:00
-- url     : https://prove2.me/theorems/fc7f29e0-84c8-4eb5-b6a0-0f3b8b038913
-- title:
--   The non-adaptive soundness game of a two-message argument
-- statement:
--   For a two-message argument and a soundness baseline $c_0 \in [0,1)$, the soundness game is the family of two-message games indexed by the statement $x$: the challenger samples $(pk, vk) \leftarrow \mathcal V_1(1^\lambda, x)$, sends $pk$, receives $\pi$ and wins precisely when $\mathcal V_2(vk, x, \pi) = 1$. Its index set is the set of false statements $x \notin L$; falsity is imposed through the index set and not checked by the challenger.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.2, p.16

import Mathlib
import Definitions.Def_LaconicBarrier_LaconicArg
import Definitions.Def_LaconicBarrier_TwoMsg

namespace LaconicBarrier

/-- The **non-adaptive soundness game** of a two-message argument with soundness baseline `c₀`, as a
family of two-message games indexed by the statement (Jain, Mathialagan, Roy, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1.2, p.16: "let `C_x` sample `(pk, vk) ← V₁(1^λ, x)`, send `pk`,
receive `π`, and output `win` precisely when `V₂(vk, x, π) = 1`"; "a constant, efficiently
computable soundness baseline `c₀ ∈ [0, 1)`"). Its index set is the false statements `x ∉ L_R`,
imposed through the index set and not checked by the challenger. -/
def LaconicArg.source (A : LaconicArg) (c₀ : ℝ) (h0 : 0 ≤ c₀) (h1 : c₀ < 1) : TwoMsg where
  coins lam x := A.vcoins lam x
  chal lam x ρ := (A.V1 lam x ρ).1
  wins lam x ρ π := A.V2 (A.V1 lam x ρ).2 x π
  c₀ := c₀
  c₀_nonneg := h0
  c₀_lt_one := h1

end LaconicBarrier


