-- Prove2me | Definitions.Def_AgnHalfMem_StreamAlg
-- name    : AgnHalfMem_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:57.631578+00:00
-- url     : https://prove2.me/theorems/03c352df-2f11-4a12-b10e-87a44ea4c1cc
-- title:
--   Randomized streaming algorithms
-- statement:
--   A **randomized streaming algorithm** with seed space $(\Omega,P)$, memory states $S$ and $T$ samples is a family $(B_\omega)_{\omega\in\Omega}$ of branching programs of length $T$ on the state set $S$ (Definition B.1), one for each value of the random seed $\omega\sim P$, drawn independently of the samples. It uses $b$ bits of memory when $|S|\le 2^b$. A deterministic algorithm is the case of a one-point seed space.
--
--   The algorithm is **measurable** when the start vertex and leaf flags depend measurably on $\omega$, every transition event $\{(\omega,x,y): \Gamma^{\omega}_v(x,y)=u\}$ is measurable, and every leaf label $(\omega,x)\mapsto \tilde h^{\omega}_v(x)$ is jointly measurable.
--
--   **Formalization Note** The paper fixes the learner to be deterministic without loss of generality (App. B, p.28); the family form covers randomized learners directly. Joint measurability is what makes "the probability of success" a probability.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), App. B, p.28

import Mathlib
import Definitions.Def_AgnHalfMem_BP

open MeasureTheory

namespace AgnHalfMem

/-- **Randomized streaming algorithm.** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), App. B, p.28: "we model the memory-bounded learner […] with a branching
program. Without loss of generality, we may assume that the learner is deterministic, since the
randomness of any randomized algorithm can be fixed to achieve at least the same success
probability."

A randomized streaming algorithm with seed space `Ω`, memory states `S` and `T` samples is a
family `A ω` of Definition B.1 branching programs of length `T` on the state type `S`, one for
each seed `ω`. A deterministic algorithm is the case `Ω = Unit`. It uses `b` bits of memory when
`Fintype.card S ≤ 2^b`, and it sees at most `T` samples (an algorithm reading fewer samples is a
program with earlier leaves).

**Formalization Note.** The seed is drawn from a probability measure `P` on `Ω`, independent of
the samples; `IsMeasurableAlg` (below) is the joint measurability needed for the success
probability to be a probability. -/
abbrev StreamAlg (Ω S X : Type*) (T : ℕ) := Ω → BP S X T

/-- Joint measurability of a randomized algorithm in (seed, sample): the start vertex and the
leaf flags are measurable in the seed, every transition event `{(ω, z) | step i v z = u}` is
measurable, and every leaf label `(ω, x) ↦ h̃(v)(x)` is jointly measurable.

**Formalization Note.** Without this condition a seed space `[0,1]` partitioned into
non-measurable sets of full outer measure would let a zero-memory algorithm "guess" any finite
family of hypotheses with outer probability one; requiring it is the meaning of "probability" in
the paper. -/
def IsMeasurableAlg {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}
    (A : StreamAlg Ω S X T) : Prop :=
  (∀ v, MeasurableSet {ω | (A ω).start = v}) ∧
  (∀ i v u, MeasurableSet {p : Ω × (X × Bool) | (A p.1).step i v p.2 = u}) ∧
  (∀ i v, MeasurableSet {ω | (A ω).isLeaf i v = true}) ∧
  (∀ i v, Measurable (fun p : Ω × X => (A p.1).out i v p.2))

end AgnHalfMem


