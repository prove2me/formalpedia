-- Prove2me | Definitions.Def_UninformedMG_IsJoint
-- name    : UninformedMG_IsJoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:26.644438+00:00
-- url     : https://prove2.me/theorems/71613550-d86f-4d72-8fb8-cc2c87bb7317
-- title:
--   Joint variable $z=w\pi$, its weights and policies (Eqs. (3)–(4)), and the mixture policy $\mu^{z,q}$
-- statement:
--   The **joint domain** is
--   $$\mathcal Z=\Big\{z=\{z_{h,s,v,a}\}\ge0:\ \exists w\in\Delta(\mathcal V),\ \sum_{a\in A_h}z_{h,s,v,a}=w(v)\ \ \forall h,s,v\Big\}.$$
--   Each $z\in\mathcal Z$ induces the weights $w(v)=\sum_az_{h,s,v,a}$ and the policies $\pi_h(a\mid s,v)=z_{h,s,v,a}/w(v)$ when $w(v)>0$, with $\pi_h(\cdot\mid s,v)$ any distribution when $w(v)=0$. Conversely every pair with $w\in\Delta(\mathcal V)$ and $\pi_h(\cdot\mid s,v)\in\Delta(A_h)$ gives $z_{h,s,v,a}=w(v)\pi_h(a\mid s,v)\in\mathcal Z$.
--
--   A **mixing table** $q_h(v\mid s)$ combines the candidate policies into the **mixture policy**
--   $$\mu^{z,q}_h(a\mid s)=\sum_vq_h(v\mid s)\pi_h(a\mid s,v).$$
--
--   **Formalization Note** A joint variable is represented by its pair $(w,\pi)$. Pairs that differ only at candidates with $w(v)=0$ represent the same $z$, and every quantity of the mission evaluated at a pair is unchanged by such a change wherever the paper evaluates it.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Eqs. (3)–(4), p.5 (PDF p.7); mixture policy, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_UninformedMG_CandClass

namespace UninformedMG

variable {H : ℕ}

/-- Candidate-conditional action distributions `π_h(a | s, v)` (Eq. (4), p.5). -/
abbrev CPolicy {G : Game H} (V : CandClass G) :=
  (h : Fin H) → G.St h.castSucc → V.C → G.Act h → ℝ

/-- Local mixing tables `q_h(v | s)` (Section 1.4, p.6). -/
abbrev Mixing {G : Game H} (V : CandClass G) := (h : Fin H) → G.St h.castSucc → V.C → ℝ

/-- **Joint variable** (Eqs. (3)–(4), p.5 = PDF p.7). `Z` is the set of nonnegative
`z_{h,s,v,a}` for which some `w ∈ Δ(V)` has `∑_{a} z_{h,s,v,a} = w(v)` for all `h, s, v`; each `z`
induces the weight `w(v) = ∑_a z_{h,s,v,a}` and the policy `π_h(a|s,v) = z_{h,s,v,a}/w(v)` when
`w(v) > 0` (any distribution when `w(v) = 0`). `IsJoint V w π` says that `(w, π)` is such a pair:
`w ∈ Δ(V)` and `π_h(· | s, v) ∈ Δ(A_h)`; it represents `z_{h,s,v,a} = w(v) π_h(a | s, v)`.

**Formalization Note.** Every `z ∈ Z` has this form by Eq. (4), and every pair gives an element
of `Z`. Pairs that differ only at candidates with `w(v) = 0` represent the same `z`; every
quantity of the mission that takes a pair (`drift`, `Jbar`, `feasibleMix`, `divRes`, `pairing`)
is unchanged by such a change wherever the paper uses it. -/
def IsJoint {G : Game H} (V : CandClass G) (w : V.C → ℝ) (π : CPolicy V) : Prop :=
  w ∈ stdSimplex ℝ V.C ∧ ∀ h s v, π h s v ∈ stdSimplex ℝ (G.Act h)

/-- The **mixture policy** `μ^{z,q}_h(a | s) = ∑_v q_h(v | s) π_h(a | s, v)` (p.11, under Eq. (22);
Algorithm 1, p.12). -/
noncomputable def mixPol {G : Game H} (V : CandClass G) (q : Mixing V) (π : CPolicy V) :
    LPolicy G :=
  fun h s a => ∑ v, q h s v * π h s v a

end UninformedMG


