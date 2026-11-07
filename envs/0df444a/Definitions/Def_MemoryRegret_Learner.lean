-- Prove2me | Definitions.Def_MemoryRegret_Learner
-- name    : MemoryRegret_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:23.680762+00:00
-- url     : https://prove2.me/theorems/2bc7b4dc-8bdc-49d1-a0dd-a99964c54b7b
-- title:
--   Randomized online learner with finite memory; regret guarantee
-- statement:
--   A **learner** with state space $\sigma$ for horizon $T$ keeps a state in the finite set $\sigma$ between rounds; its memory is $\log_2|\sigma|$ bits. Before the first round it draws a random seed $\omega$ from a distribution on a finite set $\Omega$, independently of the sequence, and starts in the state $s_0(\omega)$. At round $t$, in state $s$, it observes $x_t$, predicts $\hat y_t=p_t^\omega(s,x_t)$, observes $y_t$ and moves to $u_t^\omega(s,x_t,y_t)$; the rules may depend on the round and on the seed.
--
--   On a sequence $z=((x_t,y_t))_t$ the mistakes are $\sum_t\mathbf 1\{\hat y_t\ne y_t\}$ and those of a hypothesis $h$ are $\sum_t\mathbf 1\{h(x_t)\ne y_t\}$. The learner **achieves regret $R$ with respect to $H$ with probability at least $q$** if for every sequence $z$, fixed in advance (an oblivious adversary),
--   $$\Pr\Bigl[\forall h\in H:\ \sum_t\mathbf 1\{\hat y_t\ne y_t\}\le\sum_t\mathbf 1\{h(x_t)\ne y_t\}+R\Bigr]\ge q.$$
--
--   For nonempty $H$ this says that $\mathrm{Reg}_H(T)$ of eq. (1) is at most $R$ with probability at least $q$.
--
--   **Formalization Note** A randomized learner is a distribution over deterministic finite-state learners, the convention the paper uses for randomized branching programs (p.12: "there exists a fixing to randomness"); the seed is not counted as memory. This contains learners that draw fresh random bits every round (take $\Omega$ to be the product of the per-round randomness), and since $X$, $\sigma$ and the horizon are finite, every randomized learner with $S$ bits of state is of this form with $|\sigma|\le2^S$.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §1.1, eq. (1), p.3

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec

namespace MemoryRegret

/-- **A randomized online learner with finite memory (§1.1, p.3).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§1.1, p.3: "On each round t, a learner observes an instance x_t ∈ X, predicts a binary label
ŷ_t, and then observes the true label y_t. … We measure memory by the number of bits of state
retained by the learner between rounds."

A `Learner X σ T Ω` keeps a state in the type `σ` between rounds. Before the first round it
draws a random seed `ω` from the probability vector `seedLaw` on the finite type `Ω`,
independently of the sequence, and starts in the state `init ω`. At round `t < T`, in state
`s`, it sees `x_t`, predicts `predict ω t s x_t`, sees `y_t`, and moves to
`update ω t s x_t y_t`. The memory of the learner is `log₂ |σ|` bits.

**Formalization Note.** A randomized learner is a probability distribution over deterministic
finite-state learners (the convention the paper uses for branching programs, p.12: "there
exists a fixing to randomness"); the rules may depend on the round (a non-uniform learner).
This contains the learners that draw fresh random bits at every round (take `Ω` to be the
product of the per-round randomness), and, since `X`, `σ` and the horizon are finite, every
randomized learner with `S` bits of state is of this form with `|σ| ≤ 2^S` and a finite `Ω`.
The seed is not counted as memory; the paper's argument (Theorem 11 → a randomized branching
program → Theorem 4) treats the learner's randomness the same way. -/
structure Learner (X σ : Type) (T : ℕ) (Ω : Type) [Fintype Ω] where
  seedLaw : Ω → ℝ
  seedLaw_prob : IsProbVec seedLaw
  init : Ω → σ
  predict : Ω → Fin T → σ → X → Bool
  update : Ω → Fin T → σ → X → Bool → σ

namespace Learner

variable {X σ Ω : Type} [Fintype Ω] {T : ℕ}

/-- The state before round `t` of the run with seed `ω` on the sequence
`z = ((x_0, y_0), …, (x_{T−1}, y_{T−1}))`. -/
def stateSeq (L : Learner X σ T Ω) (ω : Ω) (z : Fin T → X × Bool) : ℕ → σ
  | 0 => L.init ω
  | t + 1 =>
    if h : t < T then L.update ω ⟨t, h⟩ (stateSeq L ω z t) (z ⟨t, h⟩).1 (z ⟨t, h⟩).2
    else stateSeq L ω z t

/-- The predictions `ŷ_0, …, ŷ_{T−1}` of that run: `ŷ_t` depends only on the seed, the state
before round `t` (a function of the seed and `x_0, y_0, …, x_{t−1}, y_{t−1}`) and on `x_t`. -/
def predictions (L : Learner X σ T Ω) (ω : Ω) (z : Fin T → X × Bool) : Fin T → Bool :=
  fun t => L.predict ω t (L.stateSeq ω z t) (z t).1

open Classical in
/-- `Pr[ŷ ∈ E]` for the learner run on the fixed (oblivious) sequence `z`, over the seed. -/
noncomputable def runProb (L : Learner X σ T Ω) (z : Fin T → X × Bool)
    (E : (Fin T → Bool) → Prop) : ℝ :=
  ∑ ω, L.seedLaw ω * if E (L.predictions ω z) then 1 else 0

end Learner

/-- The number of mistakes `∑_t 1{ŷ_t ≠ y_t}` of predictions `ŷ` on the sequence `z`. -/
def mistakes {X : Type} {T : ℕ} (ŷ : Fin T → Bool) (z : Fin T → X × Bool) : ℕ :=
  (Finset.univ.filter fun t => ŷ t ≠ (z t).2).card

/-- The number of mistakes `∑_t 1{h(x_t) ≠ y_t}` of a hypothesis `h` on `z`. -/
def mistakesOf {X : Type} {T : ℕ} (h : X → Bool) (z : Fin T → X × Bool) : ℕ :=
  (Finset.univ.filter fun t => h (z t).1 ≠ (z t).2).card

/-- `AchievesRegret H L R q`: against every obliviously chosen sequence `z ∈ (X × {0,1})^T`,
with probability at least `q` over the learner's randomness, the learner's mistakes exceed
those of every `h ∈ H` by at most `R`, i.e. `Reg_H(T) ≤ R` with `Reg_H(T)` as in eq. (1), p.3
(for nonempty `H`, "for all `h ∈ H`" is "against `min_{h∈H}`"). -/
def AchievesRegret {X σ Ω : Type} [Fintype Ω] {T : ℕ}
    (H : Set (X → Bool)) (L : Learner X σ T Ω) (R q : ℝ) : Prop :=
  ∀ z : Fin T → X × Bool,
    q ≤ L.runProb z (fun ŷ => ∀ h ∈ H, (mistakes ŷ z : ℝ) ≤ mistakesOf h z + R)

end MemoryRegret


