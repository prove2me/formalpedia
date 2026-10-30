-- Prove2me | Definitions.Def_BBPSSW_Distill_distillableEntanglement
-- name    : BBPSSW_Distill_distillableEntanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:47:19.953844+00:00
-- url     : https://prove2.me/theorems/59efeecf-d677-40de-b512-e48650473b11
-- title:
--   Distillable entanglement $D(M)$
-- statement:
--   The distillable entanglement of a two-spin state $M$ is the supremum of its achievable singlet rates,
--
--   $$D(M)=\sup\{\,r\ge0:\ r\text{ is achievable from }M\,\}\in[0,\infty].$$
--
--   It is the asymptotic yield of near-perfect singlets per copy of $M$ by local operations and classical communication.
--
--   **Formalization Note** The paper describes $D(M)$ in words only; this is the standard operational reading. The supremum is taken in $[0,\infty]$, so it is $0$ when only rate $0$ (or no rate) is achievable.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Abstract, p. 1 and p. 4 ("the optimal asymptotic yield D(M) of purified singlets distillable from general mixed states M")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_AchievableRate

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)
open scoped NNReal ENNReal

namespace BBPSSW.Distill

/-- **The distillable entanglement `D(M)`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Abstract, p. 1: "We give upper and lower bounds on the yield D(M) of pure singlets
(|Ψ−⟩) distillable from mixed states M"; p. 4: "the optimal asymptotic yield D(M) of purified
singlets distillable from general mixed states M".

`D(M)` is the supremum of the achievable rates `r` (`AchievableRate M r`), taken in
`[0, ∞]`.

**Formalization Note.** The paper defines D(M) in words only; this is the standard operational
reading (finite-round two-way LOCC, output fidelity with singlets tending to one, exact rate
limit). The supremum is in `ℝ≥0∞`, so it is `0` when no rate is achievable and is never a
junk value of an unbounded real supremum. -/
noncomputable def distillableEntanglement (M : Matrix QQ QQ ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : AchievableRate M r), (r : ℝ≥0∞)

end BBPSSW.Distill


