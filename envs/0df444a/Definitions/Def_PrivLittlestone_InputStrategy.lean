-- Prove2me | Definitions.Def_PrivLittlestone_InputStrategy
-- name    : PrivLittlestone_InputStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:55.0242+00:00
-- url     : https://prove2.me/theorems/9462b697-010e-4a0d-8d07-d72e2de52692
-- title:
--   Adaptive input strategy seeing the current classifier
-- statement:
--   An **adaptive input strategy** for horizon $T$ chooses, at each round $t$, the record $z_t = (x_t, y_t)$ as a function of the classifiers $g_1, \dots, g_t$ released so far, **including the current one** $g_t$.
--
--   This is the input model of the paper's adaptive accuracy guarantees ("allow the adversary to observe $g_t$ before choosing $z_t$"); a fixed stream is the special case that ignores the classifiers.
--
--   **Formalization Note** Deterministic (fixed coins); a randomized strategy is a mixture of deterministic ones, and probability bounds for each of them integrate.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib

namespace PrivLittlestone

/-- An **adaptive input strategy** for a horizon `T` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§2.1, p.4: "Our adaptive accuracy guarantees allow the adversary to observe `g_t` before choosing
`z_t`"): at the 0-based round `t` it sees the classifiers `g_0, …, g_t` released so far, including
the current one, and supplies the record `z_t = (x_t, y_t)`.

**Formalization Note** A deterministic strategy (fixed adversary coins); a randomized adversary is
a mixture of these, and probability bounds for every deterministic strategy integrate to it. -/
abbrev InputStrategy (X : Type*) (T : ℕ) : Type _ :=
  (t : Fin T) → (Fin (t.val + 1) → X → Bool) → X × Bool

end PrivLittlestone


