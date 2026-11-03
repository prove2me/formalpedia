-- Prove2me | Definitions.Def_WeightedCongestionBR_PhasePrefix
-- name    : WeightedCongestionBR_PhasePrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:26.155448+00:00
-- url     : https://prove2.me/theorems/85931909-9d79-4463-b749-f8ea93616837
-- title:
--   Prefix of a phase of Algorithm 1
-- statement:
--   A list of configurations $c, c_1,\dots$ is a prefix of phase $i$ if $c$ is the configuration at which phase $i$ begins (the initial configuration for $i=0$, otherwise a reachable configuration produced by the end of phase $i-1$) and the list continues with steps of Algorithm 1 that stay in phase $i$, that is, best-response moves. The state of $c$ is $s^{i-1}$ (with $s^{-1}=s_{\mathrm{init}}$).
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The phase need not have ended; a complete phase is `PhaseRun`.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §4.2, p.14

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_AlgStep
import Definitions.Def_WeightedCongestionBR_Reach
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- A **prefix of a phase** of Algorithm 1 (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.14): a list `l = c :: rest` of configurations in
which `c` is the configuration at which some phase `i` begins — the initial configuration for `i = 0`,
or a reachable configuration reached by the end-of-phase step of phase `i − 1` — and `l` continues
with steps of `AlgStep` that all stay in phase `i` (best-response moves). Then `c.s = s^{i−1}` (with
`s^{−1} := s_init`) and the movers of `l` are the players that moved in phase `i` so far.

**Formalization Note** The phase need not have ended; `PhaseRun` adds that it has. -/
def PhasePrefix {n r : ℕ} (G : Game n r) (d m : ℕ) (sinit : G.Profile) (l : List (Config G)) :
    Prop :=
  ∃ (c : Config G) (rest : List (Config G)), l = c :: rest ∧
    (c = ⟨0, sinit, ∅⟩ ∨
      ∃ c0 : Config G, Reach G d m sinit c0 ∧ AlgStep G d m sinit c0 c ∧ c.phase = c0.phase + 1) ∧
    l.IsChain (AlgStep G d m sinit) ∧ ∀ c' ∈ l, c'.phase = c.phase

end WeightedCongestionBR


