-- Prove2me | Definitions.Def_NashOrTriangle_IsPairAnswer
-- name    : NashOrTriangle_IsPairAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:48.034653+00:00
-- url     : https://prove2.me/theorems/9932d892-a032-43d8-9c9d-640818dace3d
-- title:
--   Halted with a strategy pair of gap at most $\varepsilon$
-- statement:
--   The run has halted and its output is a strategy pair $(p, q)$ of finite rational mixtures of **known** rows and columns whose gap in the full game satisfies
--   $$
--   D(p, q) = U(q) - L(p) \le \varepsilon .
--   $$
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Theorem 2.1, pp.4–5 (PDF pp.5–6)

import Mathlib
import Definitions.Def_NashOrTriangle_decode
import Definitions.Def_NashOrTriangle_gap

namespace NashOrTriangle

/-- The state has halted with a strategy pair of gap at most `ε`: the output decodes to a pair of
label mixtures `(p, q)` that are finite rational mixtures of **known** rows and columns, and the
strategy pair they name has `D(p, q) = U(q) − L(p) ≤ ε`, computed in the full game.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 2.1, printed pp. 4–5 (PDF pp. 5–6): "returns either a pair (p, q) with
D(p, q) ≤ 1/k …"; Definition 1.1, printed p. 3 (PDF p. 4): outputs are finitely supported with
rational probabilities. -/
def IsPairAnswer {A B : Type*} (M : A → B → ℚ) (ε : ℝ) (s : State A B) : Prop :=
  ∃ base : ℤ, ∃ p q : ℕ →₀ ℚ, s.output = some base ∧
    decode s.core.mem base = some (Answer.pair p q) ∧
    ValidLabelMix s.rows.length p ∧ ValidLabelMix s.cols.length q ∧
    gap M (labelMix s.rows p) (labelMix s.cols q) ≤ ε

end NashOrTriangle


