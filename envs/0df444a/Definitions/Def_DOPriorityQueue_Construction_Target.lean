-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Target
-- name    : DOPriorityQueue_Construction_Target
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:36.677093+00:00
-- url     : https://prove2.me/theorems/93cd6516-74f2-4115-8668-75964d6177ed
-- title:
--   Theorem 4.1 — uniform execution contract
-- statement:
--   Fix $c>0$ and $\varepsilon>0$. The headline contract quantifies one finite program, positive fixed word-length parameters, positive uniform work and space constants, a positive integer space exponent, and a threshold at least $16$, all before the public horizon or actual history. The word length is an affine positive multiple of $\lceil\log_2T\rceil$ and must accommodate the horizon, priority universe and program counter.
--
--   At every $T\ge2$ the program must terminate with exact stable answers on every random tape and satisfy full-operation $(\varepsilon,\delta_T)$ differential obliviousness, with a normalized trace law and
--   $$\delta_T=2^{-\lceil\log_2T\rceil^2},\qquad U=\lfloor T^c\rfloor.$$
--   Beyond the fixed threshold, every history of length $t\le T$ must satisfy the uniform expected total-work bound $C t\log T/\log\log T$ and a pathwise private-word bound $D\lceil\log_2T\rceil^k$, including all temporary storage.
--
--   The rate uses natural logarithms, an asymptotically equivalent convention. The threshold avoids the small-horizon singularity; exactness and privacy include all horizons $T\ge2$. No queue implementation or guarantee is a field supplied by the existential program. This contract records the full chosen goal.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 6, Theorem 4.1; pp. 26–27, its proof

import Definitions.Def_DOPriorityQueue_Construction_Execution

set_option autoImplicit false

namespace DOPriorityQueue.Construction

/-- All logarithms in public integer parameters are base two. -/
def horizonLog (T : ℕ) : ℕ := Nat.clog 2 T

noncomputable def deltaT (T : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((horizonLog T) ^ 2 : ℤ))

/-- The source's [T^c] has integer endpoints and includes 0 < c < 1. -/
noncomputable def priorityMaximum (c : ℝ) (T : ℕ) : ℕ :=
  ⌊(T : ℝ) ^ c⌋₊

/-- Used only beyond a threshold T₀ ≥ 16 in the target contract. -/
noncomputable def workRate (T : ℕ) : ℝ :=
  Real.log (T : ℝ) / Real.log (Real.log (T : ℝ))

/-- The word length is Θ(log T), with fixed positive scale and fixed offset. -/
def wordLength (scale offset T : ℕ) : ℕ := scale * horizonLog T + offset

/-- Each clause is a proposition about executions of finite code. No structure
field supplies a queue transition, a probability law, a cost, or a guarantee.
This target is existential over real programs; the construction is not defined here.
All constants and the code precede T and the actual history. -/
noncomputable def HeadlineTarget (c ε : ℝ) : Prop :=
  ∃ (program : List RAM.Instruction) (scale offset exponent threshold : ℕ)
    (workConstant spaceConstant : ℝ),
    0 < scale ∧ 0 < offset ∧ 0 < exponent ∧ 16 ≤ threshold ∧
    0 < workConstant ∧ 0 < spaceConstant ∧
    (∀ T : ℕ, 2 ≤ T →
      let w := wordLength scale offset T
      let U := priorityMaximum c T
      T < 2 ^ w ∧ U < 2 ^ w ∧ program.length + 1 < 2 ^ w ∧
      (∀ (Ball : Type) (history : List (Operation Ball)), validHistory T U history →
        RAM.exactOnHistory (w := w) program T U history ∧
        RAM.traceProbability (w := w) program T U history Set.univ = 1) ∧
      RAM.isDO w T U program ε (deltaT T)) ∧
    (∀ T : ℕ, threshold ≤ T →
      let w := wordLength scale offset T
      let U := priorityMaximum c T
      ∀ (Ball : Type) (history : List (Operation Ball)), validHistory T U history →
        RAM.expectedWork (w := w) program T U history ≤
          ENNReal.ofReal (workConstant * (history.length : ℝ) * workRate T) ∧
        ∀ fuel coins result,
          RAM.runHistory program fuel (RAM.initialState w T U Ball) coins history = some result →
          (result.peakPrivate : ℝ) ≤ spaceConstant * (horizonLog T : ℝ) ^ exponent)

end DOPriorityQueue.Construction


