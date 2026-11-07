-- Prove2me | Definitions.Def_MemoryRegret_RandOnlineAlg
-- name    : MemoryRegret_RandOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:19.672528+00:00
-- url     : https://prove2.me/theorems/93a23549-823b-4eef-966e-ecfa42f811f6
-- title:
--   Randomized online prediction algorithm; flattening a stream
-- statement:
--   A (possibly randomized) **online prediction algorithm** draws a seed $\omega$ from a distribution on a finite set, independently of the data, and at round $t$ predicts as a function of $\omega$, all past examples $(x_s,y_s)_{s<t}$ and the current instance $x_t$. It has no memory bound.
--
--   A stream of $T_{\mathrm{block}}$ elements $(x_{t'},b_{t'})$ with $b_{t'}\in\{0,1\}^m$ is **flattened** into $T=m\,T_{\mathrm{block}}$ labeled examples: round $t=t'm+i$ (0-based) is $(x_{t'},b_{t'}^{(i)})$. The number of mistakes in block $j$ is denoted $M_j$.
--
--   **Formalization Note** Over a finite horizon with finite $X$, every randomized algorithm is a mixture of finitely many deterministic ones, so a finite seed set is general. Lemma 6.2 has no instances and uses $X$ a singleton.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), §6.1, p.34; Theorem 12, p.34

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_Learner

namespace MemoryRegret

/-- **A (possibly randomized) online prediction algorithm without a memory bound.**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
§6.1, p.34: "we define an online prediction algorithm to be any algorithm that picks Ŷ_t in each
round t after having observed Y_1, …, Y_{t−1}"; Theorem 12, p.34: "any (possibly randomized)
online learning algorithm".

A `RandOnlineAlg X T Ω` draws a seed `ω` from the probability vector `seedLaw` on the finite
type `Ω`, independently of the data; at round `t` it predicts `predict ω t past x_t`, where
`past = ((x_0, y_0), …, (x_{t−1}, y_{t−1}))`.

**Formalization Note.** Over a finite horizon with finite `X`, every randomized algorithm is a
mixture of finitely many deterministic ones, so a finite seed type is general. Lemma 6.2 has no
instances; it uses `X = Unit`. -/
structure RandOnlineAlg (X : Type) (T : ℕ) (Ω : Type) [Fintype Ω] where
  seedLaw : Ω → ℝ
  seedLaw_prob : IsProbVec seedLaw
  predict : Ω → (t : Fin T) → (Fin t → X × Bool) → X → Bool

namespace RandOnlineAlg

variable {X Ω : Type} [Fintype Ω] {T : ℕ}

/-- The predictions of `A` with seed `ω` on the sequence `z`. -/
def preds (A : RandOnlineAlg X T Ω) (ω : Ω) (z : Fin T → X × Bool) : Fin T → Bool :=
  fun t => A.predict ω t (fun j => z (Fin.castLE t.2.le j)) (z t).1

/-- The number of mistakes of `A` with seed `ω` on `z`. -/
def algMistakes (A : RandOnlineAlg X T Ω) (ω : Ω) (z : Fin T → X × Bool) : ℕ :=
  mistakes (A.preds ω z) z

end RandOnlineAlg

/-- The block length is positive whenever the flattened horizon `m · T_block` has a round. -/
theorem flat_pos {m Tb : ℕ} (t : Fin (m * Tb)) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; exact absurd t.2 (by simp)
  · exact h

/-- The flattening of a stream of `T_block` blocks into `T = m · T_block` labeled examples
(Theorem 12, p.34): round `t = t′·m + i` (0-based) is `(x_{t′}, b_{t′}^{(i)})`. -/
def flattenStream {X : Type} {m Tb : ℕ} (s : Fin Tb → X × (Fin m → Bool)) :
    Fin (m * Tb) → X × Bool :=
  fun t =>
    let j : Fin Tb := ⟨t / m, Nat.div_lt_of_lt_mul t.2⟩
    ((s j).1, (s j).2 ⟨t % m, Nat.mod_lt _ (flat_pos t)⟩)

/-- `M_j`: the number of mistakes of `A` (seed `ω`) in block `j` of the flattened stream. -/
def blockMistakes {X Ω : Type} [Fintype Ω] {m Tb : ℕ} (A : RandOnlineAlg X (m * Tb) Ω) (ω : Ω)
    (s : Fin Tb → X × (Fin m → Bool)) (j : Fin Tb) : ℕ :=
  (Finset.univ.filter fun t : Fin (m * Tb) =>
    (t : ℕ) / m = j ∧ A.preds ω (flattenStream s) t ≠ (flattenStream s t).2).card

end MemoryRegret


