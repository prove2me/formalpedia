-- Prove2me | Definitions.Def_MWCSherali_MWCHardOn
-- name    : MWCSherali_MWCHardOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:49.06093+00:00
-- url     : https://prove2.me/theorems/32948f2d-4f54-4b16-bb3c-1d2909f79428
-- title:
--   NP-hardness of approximating Multiway Cut within $\rho$ on a class of terminal counts
-- statement:
--   Let $P$ be a property of the number of terminals and $\rho\in\mathbb R$. **Multiway Cut on instances with $P(k)$ is NP-hard to approximate within $\rho$** when there are thresholds $c>0$ and $s>\rho c$ such that, for every NP language $L$, there is a polynomial-time reduction mapping members of $L$ to **Yes** instances and non-members to **No** instances, where (with $W$ the total weight)
--
--   1. **Yes:** $P(k)$, $k\ge1$, $W>0$, and some multiway cut has weight at most $cW$;
--   2. **No:** $P(k)$, $k\ge1$, $W>0$, and every multiway cut has weight at least $sW$.
--
--   A polynomial-time algorithm with approximation ratio $\rho$ would separate the two sets, because $\rho cW<sW$.
--
--   Here $W$ is `Max3CutHard.wt` of the graph and the weight of a multiway cut $g$ is `Max3CutHard.cutK`, the total weight of the edges whose endpoints get different labels.
--
--   **Formalization Note** NP-hardness is the published `OptInapprox.MaxCut.GapNPHard` (Karp reductions from every NP language over every finite alphabet) applied to the encoding `encMWC`. The ratio is strict ($\rho c<s$). The condition $k\ge1$ keeps instances without any multiway cut out of the No set.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 1.1, p.2; Theorem 2.2, p.14 ("NP-hard to approximate Multiway Cut ... within a factor of")

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_MWCSherali_MWCInst
import Definitions.Def_Max3CutHard_wt
import Definitions.Def_Max3CutHard_cutK
import Definitions.Def_MWCSherali_MWCInst_IsTerminalLabeling
import Definitions.Def_MWCSherali_encMWC

namespace MWCSherali

open OptInapprox.MaxCut

/-- **NP-hardness of approximating Multiway Cut within `ρ`, on instances whose number of
terminals satisfies `P`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3,
2026), Theorem 1.1, p.2, and Theorem 2.2, p.14 ("it is NP-hard to approximate Multiway Cut ...
within a (multiplicative) factor of `ρ`").

`MWCHardOn P ρ` holds when there are thresholds `0 < c` and `s > ρ·c` such that it is NP-hard
(Karp reductions from every NP language, `OptInapprox.MaxCut.GapNPHard`) to distinguish
* **Yes** instances: some multiway cut has weight at most `c·W`, from
* **No** instances: every multiway cut has weight at least `s·W`,

where `W > 0` is the total weight, the number of terminals `k` satisfies `P k` and `k ≥ 1`.
A polynomial-time algorithm with approximation ratio `ρ` would separate the two sets, since
`ρ·c·W < s·W`.

**Formalization Note.**
* The gap ratio is strict (`ρ·c < s`); with `s = ρ·c` a `ρ`-approximation could not tell the sets
  apart.
* `1 ≤ k` keeps instances without any multiway cut out of the No set (they would satisfy the
  universal clause vacuously). `0 < W` excludes the empty graph.
* Weights are unary multigraph multiplicities (`MWCInst`); `W` is the published `Max3CutHard.wt`
  and the weight of a multiway cut `g` is the published `Max3CutHard.cutK` (edges whose endpoints
  get different labels). -/
def MWCHardOn (P : ℕ → Prop) (ρ : ℝ) : Prop :=
  ∃ c s : ℝ, 0 < c ∧ ρ * c < s ∧
    GapNPHard encMWC
      (fun G : MWCInst => P G.k ∧ 1 ≤ G.k ∧ 0 < Max3CutHard.wt G.graph ∧
        ∃ g, G.IsTerminalLabeling g ∧
          (Max3CutHard.cutK G.k G.graph g : ℝ) ≤ c * Max3CutHard.wt G.graph)
      (fun G : MWCInst => P G.k ∧ 1 ≤ G.k ∧ 0 < Max3CutHard.wt G.graph ∧
        ∀ g, G.IsTerminalLabeling g →
          s * Max3CutHard.wt G.graph ≤ (Max3CutHard.cutK G.k G.graph g : ℝ))

end MWCSherali


