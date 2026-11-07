-- Prove2me | Definitions.Def_DynHaussler_gamePlay
-- name    : DynHaussler_gamePlay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:39.760966+00:00
-- url     : https://prove2.me/theorems/afa81706-9151-4822-a7bc-d65ba03fe597
-- title:
--   Play of the input–action game between deterministic strategies
-- statement:
--   In the game of Lemma 32, a **deterministic adversary strategy** $\alpha$ maps each history of completed rounds to an input, and a **deterministic constructor strategy** $\kappa$ maps each history and current input to an action. Both players observe all earlier moves, and the constructor also observes the current input. The **play** of the first $t$ rounds is built round by round: from the history $h$ of the completed rounds the next round is $(\alpha(h),\kappa(h,\alpha(h)))$.
--
--   **Formalization Note** A history of $t$ rounds is a map `Fin t → I × A`; the play is defined by recursion on $t$, appending one round at a time.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 32, p.43 (PDF p.45)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **play** of the first `t` rounds of the input–action game of Lemma 32 between a
deterministic adversary strategy `α` and a deterministic constructor strategy `κ`: in each round
the adversary first chooses an input from the preceding history, and the constructor then chooses
an action from the preceding history and the current input. Both players observe all earlier
moves, and the constructor also observes the current input.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Lemma 32, p.43 (PDF p.45).

**Formalization Note** A history of `t` completed rounds is `Fin t → I × A` (0-based); the play
is built by appending `(α h, κ h (α h))` to the history `h` round by round. -/
def gamePlay {I A : Type*} (α : (t : ℕ) → (Fin t → I × A) → I)
    (κ : (t : ℕ) → (Fin t → I × A) → I → A) : (t : ℕ) → Fin t → I × A
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (α := fun _ => I × A) (gamePlay α κ t)
      (α t (gamePlay α κ t), κ t (gamePlay α κ t) (α t (gamePlay α κ t)))

end DynHaussler


