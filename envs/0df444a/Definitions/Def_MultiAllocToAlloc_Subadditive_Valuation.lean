-- Prove2me | Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
-- name    : MultiAllocToAlloc_Subadditive_Valuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:09:12.381268+00:00
-- url     : https://prove2.me/theorems/7534dcfe-004f-492e-ac1f-77d509e3fb60
-- title:
--   Normalized and monotone valuations, and the largest single-item value δ
-- statement:
--   Items are `Fin m` and a valuation is a real set function `v : Finset (Fin m) → ℝ`. It is **normalized** when $v(\emptyset)=0$ and **monotone** when $v(S)\le v(T)$ for all $S\subseteq T$ (p. 1). Subadditivity is the published predicate `SubmodOrder.Subadditive` ($v(S\cup T)\le v(S)+v(T)$), stated as a separate hypothesis. For a bundle $S$, `maxItemValue v S` is $\delta=\max_{e\in S} v(\{e\})$ (Theorem 1, p. 2) when $S\neq\emptyset$, and $0$ when $S=\emptyset$, where the paper's maximum is undefined.
-- source:
--   Feige, arXiv:2506.21493v1, §1, p. 1, and Theorem 1, p. 2

import Mathlib

namespace MultiAllocToAlloc.Subadditive

/-- Normalized valuation (Feige, arXiv:2506.21493v1, §1, p. 1): `v(∅) = 0`. -/
def IsNormalized {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0

/-- Monotone valuation (Feige, arXiv:2506.21493v1, §1, p. 1): `v(S) ≤ v(T)` whenever `S ⊆ T`. -/
def IsMonotone {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), S ⊆ T → v S ≤ v T

/-- `δ` of a bundle (Feige, arXiv:2506.21493v1, Theorem 1, p. 2): the largest value
`max_{e ∈ S} v({e})` of a single item of `S`. On the empty bundle the value is `0`
(the maximum over the empty set is not defined by the paper). -/
noncomputable def maxItemValue {m : ℕ} (v : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun e => v {e}) else 0

end MultiAllocToAlloc.Subadditive


