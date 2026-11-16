-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsAbsorbingChain
-- name    : MetricMinTest_Supplement_IsAbsorbingChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:37:11.775136+00:00
-- url     : https://prove2.me/theorems/3aee5fed-83b4-400a-8153-018d7e5e598a
-- title:
--   Absorbing chain reaching the boundary $V_\partial$
-- statement:
--   Let $V^\circ=I\sqcup V_\partial$ be a finite vertex set with nonempty boundary $V_\partial$ and $\Gamma$ a transition matrix on $V^\circ$ (nonnegative entries, unit row sums) that makes $V_\partial$ absorbing ($\Gamma_{bb}=1$ for $b\in V_\partial$) and whose chain reaches $V_\partial$ almost surely from every state:
--   $$\sum_{b\in V_\partial}(\Gamma^n)_{vb}\longrightarrow1\qquad(n\to\infty)\ \text{ for every }v.$$
--   This is the setting of Theorem K.3.
--
--   **Formalization Note** Because $V_\partial$ is absorbing, $\sum_{b\in V_\partial}(\Gamma^n)_{vb}$ is the probability of having hit $V_\partial$ by time $n$ from $v$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §K.1, p.32

import Mathlib

namespace MetricMinTest.Supplement

/-- **Absorbing chain reaching the boundary** (§K.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §K.1, p.32: "Let V° = I ⊔ V∂ be a
finite vertex set with nonempty boundary V∂. A known transition matrix Γ makes V∂ absorbing; its
chain (Z_t) reaches V∂ almost surely from every state."

**Formalization Note.** `Γ` is a matrix on the finite vertex type `V` with nonnegative entries
and unit row sums; `I` is the complement of `bd = V∂`. Absorption is `Γ_bb = 1` for `b ∈ V∂`.
Because `V∂` is absorbing, `∑_{b∈V∂} (Γⁿ)_{vb}` is the probability of having hit `V∂` by time
`n` from `v`, so "reaches V∂ almost surely" is that this tends to `1` for every `v`. -/
def IsAbsorbingChain {V : Type} [Fintype V] [DecidableEq V] (Γ : Matrix V V ℝ) (bd : Finset V) :
    Prop :=
  bd.Nonempty ∧ (∀ v w, 0 ≤ Γ v w) ∧ (∀ v, ∑ w, Γ v w = 1) ∧ (∀ b ∈ bd, Γ b b = 1) ∧
  ∀ v, Filter.Tendsto (fun n : ℕ => ∑ b ∈ bd, (Γ ^ n) v b) Filter.atTop (nhds 1)

end MetricMinTest.Supplement


