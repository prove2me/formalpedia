-- Prove2me | Definitions.Def_PrivLittlestone_playClassifiers
-- name    : PrivLittlestone_playClassifiers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:47.12374+00:00
-- url     : https://prove2.me/theorems/d29a973b-64ca-400a-9ed7-d6bf2e6c84ab
-- title:
--   Classifier transcript of the adaptive game
-- statement:
--   Given an online learner $A$, an adaptive input strategy and coins $\omega$, the **classifier transcript of the adaptive game** is defined round by round: at round $t$ the learner releases $g_t$ from the records $z_1, \dots, z_{t-1}$ and $\omega$, and then the strategy, seeing $g_1, \dots, g_t$, supplies $z_t$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_OnlineLearner
import Definitions.Def_PrivLittlestone_InputStrategy

namespace PrivLittlestone

/-- The **classifier transcript of the adaptive game** between an online learner and an input
strategy over `T` rounds (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §2.1, p.4): at round `t` the
learner releases `g_t` from the records `z_0, …, z_{t−1}` and its coins, and then the strategy,
seeing `g_0, …, g_t`, supplies `z_t`.

**Formalization Note** Defined by recursion on the number of rounds played (`go t` is the list of
the first `t` classifiers); rounds are 0-based. -/
def playClassifiers {X : Type*} {T : ℕ} (A : OnlineLearner X) (inp : InputStrategy X T)
    (ω : A.Ω) : Fin T → X → Bool :=
  go T le_rfl
where
  /-- the first `t` released classifiers -/
  go : (t : ℕ) → t ≤ T → Fin t → X → Bool
    | 0, _ => Fin.elim0
    | t + 1, h =>
      Fin.snoc (α := fun _ => X → Bool) (go t (Nat.le_of_succ_le h))
        (A.release t (fun i => inp ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_succ_le h)⟩
          (fun j => go t (Nat.le_of_succ_le h)
            ⟨j, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) i.isLt⟩)) ω)

end PrivLittlestone


