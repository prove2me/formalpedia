-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_Indexable
-- name    : RelaxedIndexability_Supplement_Indexable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:02:32.601869+00:00
-- url     : https://prove2.me/theorems/e7801a10-0f8f-5967-9614-de29b1b099bc
-- title:
--   Indexability (Definition 1) and the Whittle index
-- statement:
--   Let $P(m)$ be the passive set of an arm with subsidy $m$ and discount factor $\beta$.
--
--   1. The arm is **indexable** if the passive set increases monotonically from $\emptyset$ to the whole belief simplex $\mathbb X$ as $m$ increases from $-\infty$ to $+\infty$:
--   $$
--   m\le m'\ \Rightarrow\ P(m)\subseteq P(m'),\qquad \bigcap_{m\in\mathbb R}P(m)=\emptyset,\qquad \bigcup_{m\in\mathbb R}P(m)=\mathbb X.
--   $$
--   2. A restless bandit with arms $1,\dots,N$ and common discount factor $\beta$ is **indexable** if every arm is.
--   3. The **Whittle index** of a belief $\omega$ is $W(\omega)=\inf\{m:\ \omega\in P(m)\}$, the infimum subsidy that makes $\omega$ passive (Definition 1 and (21)).
--
--   This is classical indexability, which Theorems 1 and 2 characterize. It differs from the relaxed indexability of Definition 2 in the published mission.
--
--   **Formalization Note** The two endpoints "from $\emptyset$" and "to the whole state space" are the intersection and the union of the monotone family. The Whittle index is a real infimum; for an indexable arm and a belief in the simplex the set is nonempty and bounded below, so it is the true infimum.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Definition 1, p.11; (21), p.15

import Mathlib
import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_Supplement_passiveSet

namespace RelaxedIndexability.Supplement

/-- **Indexability of one arm** (Liu, arXiv:2107.11939v4, Definition 1, p.11): the passive set
increases monotonically from `∅` to the whole belief simplex as the subsidy `m` increases from `−∞`
to `+∞`.

**Formalization Note.** Monotone for inclusion; the two limits of the monotone family are the
intersection over all `m` (which is `∅`) and the union over all `m` (which is the simplex). This is
classical indexability, different from `RelaxedIndexability.Arm.RelaxedIndexable` (Definition 2). -/
def ArmIndexable (β : ℝ) (A : RelaxedIndexability.Arm) : Prop :=
  Monotone (fun m : ℝ => passiveSet β A.P A.B m) ∧
    (⋂ m : ℝ, passiveSet β A.P A.B m) = ∅ ∧
    (⋃ m : ℝ, passiveSet β A.P A.B m) = stdSimplex ℝ (Fin A.K)

/-- **Indexability of a restless bandit** with arms `arms` and common discount factor `β`
(Liu, arXiv:2107.11939v4, Definition 1, p.11): every single-armed bandit with subsidy is
indexable. -/
def Indexable (β : ℝ) {N : ℕ} (arms : Fin N → RelaxedIndexability.Arm) : Prop :=
  ∀ n, ArmIndexable β (arms n)

/-- **The Whittle index** `W(ω) = inf {m : ω ∈ P(m)}` (Liu, arXiv:2107.11939v4, Definition 1, p.11,
and (21), p.15).

**Formalization Note.** A real infimum, the paper's index for an indexable arm and `ω` in the
simplex: the set of such `m` is then nonempty and bounded below. -/
noncomputable def whittleIndex (β : ℝ) (A : RelaxedIndexability.Arm) (ω : Fin A.K → ℝ) : ℝ :=
  sInf {m : ℝ | ω ∈ passiveSet β A.P A.B m}

end RelaxedIndexability.Supplement


