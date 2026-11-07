-- Prove2me | Definitions.Def_EffHorizonProphet_phaseOf
-- name    : EffHorizonProphet_phaseOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:48.08933+00:00
-- url     : https://prove2.me/theorems/141ad55e-bc06-4e0a-bf37-549a1bcc5ef5
-- title:
--   The phase of a stage
-- statement:
--   The stages $\{0,\dots,n-1\}$ are split into $S$ consecutive blocks $T_s$ of lengths $L(s)$. The map $\mathrm{phase}(i)$ returns the block containing the stage $i$.
--
--   **Formalization Note** Phases and stages are numbered from $0$, using the lexicographic numbering of pairs (phase, position in the phase).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3

import Mathlib

namespace EffHorizonProphet

/-- The phase of a stage (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3): `T_1, …, T_S` are consecutive blocks of lengths
`L s` that partition the stages.

**Formalization Note** Phases and stages are `0`-based: paper phase `s` is `s - 1` here. Mathlib's
`finSigmaFinEquiv` is the lexicographic numbering, so phases are consecutive. -/
def phaseOf {S : ℕ} (L : Fin S → ℕ) (i : Fin (∑ s, L s)) : Fin S :=
  (finSigmaFinEquiv.symm i).1

end EffHorizonProphet


