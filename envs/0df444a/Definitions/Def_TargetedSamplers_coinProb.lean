-- Prove2me | Definitions.Def_TargetedSamplers_coinProb
-- name    : TargetedSamplers_coinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:40.127213+00:00
-- url     : https://prove2.me/theorems/78f8d898-d843-40d9-b1df-8ce885f7dacb
-- title:
--   Uniform probability over coin strings
-- statement:
--   For $C\in\mathbb N$ and a property $P$ of bit strings,
--   $$\Pr_{r\in\{0,1\}^C}[P(r)]=\frac{|\{r\in\{0,1\}^C : P(r)\}|}{2^C}.$$
--   This is the probability over the random bits $r$ in Definition 4.1 and Definitions 4.19–4.20. It is the published `PunctSketch.coinProb` (the fraction of a finite coin space) on the coin space $\{0,1\}^C$, with a coin vector read as a bit list. For $C=0$ the single empty string is the whole space.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.1, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_PunctSketch_coinProb

namespace TargetedSamplers

/-- `Pr_{r ∈ {0,1}^C}[P(r)]`: the probability of `P` when `r` is uniform on the `2^C` bit strings of
length `C` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256
599d0a59…, Definition 4.1, p.20: "Pr_{r∈{0,1}^{C(n)}}[…]"), via the published
`PunctSketch.coinProb` (fraction of a finite coin space) on the coin space `{0,1}^C`, with a coin
vector read as a bit list.

**Formalization Note** The coin space `{0,1}^C` is never empty; for `C = 0` the single empty string
is the whole space. -/
noncomputable def coinProb (C : ℕ) (P : List Bool → Prop) : ℝ :=
  PunctSketch.coinProb (fun r : Fin C → Bool => P (List.ofFn r))

end TargetedSamplers


