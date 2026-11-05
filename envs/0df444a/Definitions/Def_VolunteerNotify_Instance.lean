-- Prove2me | Definitions.Def_VolunteerNotify_Instance
-- name    : VolunteerNotify_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:57.407947+00:00
-- url     : https://prove2.me/theorems/2770cd83-6540-471a-b040-557f19319844
-- title:
--   §3 — instance $(\lambda,p,g)$ of the online volunteer notification problem
-- statement:
--   An **instance** $\mathcal I=(\{\lambda_{s,t}\},\{p_{v,s}\},g)$ has $V$ volunteers, $S$ task types and $T$ periods. In each period $t$ a task of type $s$ arrives with probability $\lambda_{s,t}\ge 0$, where $\sum_s\lambda_{s,t}\le 1$, and with probability
--   $$
--   \lambda_{0,t}=1-\sum_{s=1}^S\lambda_{s,t}
--   $$
--   no task arrives. If an active volunteer $v$ is notified about a task of type $s$, she responds with probability $p_{v,s}\in[0,1]$. After a notification she stays inactive for $Z>0$ periods, where $P(Z=\tau)=g(\tau)$; $g$ is a probability mass function on $\{1,2,\dots\}$, possibly with unbounded support and infinite mean. A vector $x\in\mathbb R^{V\times S\times T}$ of notification probabilities is a `Decision`.
--
--   This structure is shared by all statements of the mission.
--
--   **Formalization Note** Indices are `Fin`-valued, with the paper's index equal to the value plus one. $g$ is a function on $\mathbb N$ with $g(0)=0$.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, §3, pp.9–10; Definition 2, p.12

import Mathlib

namespace VolunteerNotify

/-- An instance `I = ({λ_{s,t}}, {p_{v,s}}, g)` of the online volunteer notification problem,
Manshadi–Rodilitz, arXiv:2002.08474v7, §3, pp.9–10, with `V` volunteers, `S` task types and `T`
periods: arrival probabilities with `λ_{s,t} ≥ 0` and `∑_s λ_{s,t} ≤ 1`, match probabilities
`p_{v,s} ∈ [0, 1]`, and the mass function `g` of the inter-activity time `Z > 0`.

**Formalization Note.** Volunteers, types and periods are `Fin`-indexed: the paper's index is the
`Fin` value plus one. `g` is a function on all of `ℕ`, with `g 0 = 0` for `Z > 0`; a proper law
(`∑ g = 1`), which may have unbounded support and infinite mean, and may put mass beyond `T`. -/
structure Instance (V S T : ℕ) where
  /-- `lam s t` is `λ_{s,t}`, the probability that a task of type `s` arrives at `t`. -/
  lam : Fin S → Fin T → ℝ
  /-- `p v s` is the match probability `p_{v,s}`. -/
  p : Fin V → Fin S → ℝ
  /-- `g τ` is `P(Z = τ)`. -/
  g : ℕ → ℝ
  lam_nonneg : ∀ s t, 0 ≤ lam s t
  lam_sum_le_one : ∀ t, ∑ s, lam s t ≤ 1
  p_mem : ∀ v s, p v s ∈ Set.Icc (0 : ℝ) 1
  g_nonneg : ∀ τ, 0 ≤ g τ
  g_zero : g 0 = 0
  g_hasSum : HasSum g 1

/-- `λ_{0,t} := 1 − ∑_s λ_{s,t}`, the probability that no task arrives at `t`
(arXiv:2002.08474v7, §3, p.9). -/
def Instance.noTask {V S T : ℕ} (I : Instance V S T) (t : Fin T) : ℝ :=
  1 - ∑ s, I.lam s t

/-- A vector `x ∈ ℝ^{V×S×T}` of notification probabilities `x_{v,s,t}`
(arXiv:2002.08474v7, Definition 2, p.12). It is a normed space, so `fderiv` applies. -/
abbrev Decision (V S T : ℕ) : Type := Fin V → Fin S → Fin T → ℝ

end VolunteerNotify


