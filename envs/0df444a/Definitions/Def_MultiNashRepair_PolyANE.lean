-- Prove2me | Definitions.Def_MultiNashRepair_PolyANE
-- name    : MultiNashRepair_PolyANE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:35.165452+00:00
-- url     : https://prove2.me/theorems/77f7a6b2-c9ab-4999-8351-f24a208e58e3
-- title:
--   Rational $\varepsilon$-approximate Nash equilibria of $k$-player games computable in polynomial time
-- statement:
--   Fix a number of players $k$ and an accuracy $\varepsilon$. A *rational $k$-player game with payoffs in $[0,1]$* is given as a complete payoff table: each player $i$ has a nonempty finite action set $\{0,\dots,n_i-1\}$, and every payoff $U_i(a)$ is a fraction $p/q$ with $0\le p\le q$, written in binary.
--
--   **A rational $\varepsilon$-approximate Nash equilibrium of $k$-player games can be computed in polynomial time** if there are a multi-stack Turing machine $M$ and a constant $c$ such that, for every such table $G$ with input encoding of length $N$, $M$ outputs within $c(N+2)^c$ steps the encoding of a rational mixed profile $x$ (one probability vector per player, with the action counts of $G$) for which
--   $$u_i(x[i\leftarrow y_i]) - \varepsilon \le u_i(x)\qquad\text{for every player } i \text{ and every mixed } y_i .$$
--
--   This is the hypothesis and conclusion of the one-player extension (Lemma 2.1) and the conclusion of the rational initialization (Lemma 2.2).
--
--   **Formalization Note** Tables and profiles are the published `NashAmplification.Filtering.Table` / `RawProfile` with their binary encodings; the equilibrium notion is the published `IsEpsApproxNash` (mixed deviations), equivalent to $\mathrm{Reg}(x)\le\varepsilon$ by multilinearity.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 2.1 and Lemma 2.2, p.5 ("can be computed in polynomial time")

import Mathlib
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile)

namespace MultiNashRepair

/-- **A rational `ε`-approximate Nash equilibrium of `k`-player games can be computed in
polynomial time** (the hypothesis and conclusion of Lemma 2.1, p.5, and the conclusion of
Lemma 2.2, p.5, of Tang, Ding, Fang, arXiv:2611.06076).

`PolyANE k ε` holds when one multi-stack Turing machine `M` and one exponent `c` work for every
complete rational `k`-player table `G` with payoffs in `[0,1]`: on the binary encoding
`encGame G`, `M` outputs the encoding `encProfile x` of a rational profile `x` with the same
action counts within `c · (|encGame G| + 2)^c` steps, and `x` is an `ε`-approximate Nash
equilibrium of `G` (no player gains more than `ε` by any unilateral mixed deviation).

**Formalization Note.** Games are the published `NashAmplification.Filtering.Table k`
(players `Fin k`, nonempty action sets `Fin (n i)`, payoffs `num/den` with `num ≤ den`, possibly
unreduced); profiles are `RawProfile k`, read as real mixed profiles by `RawProfile.on`. The
ε-approximate Nash equilibrium is the published `DGPNash.WellSupported.IsEpsApproxNash` (mixed
deviations), which is equivalent to the paper's `Reg(x) ≤ ε` (pure deviations) by
multilinearity. The time bound `c (N + 2)^c` in the input length `N` is "polynomial time". -/
def PolyANE (k : ℕ) (ε : ℝ) : Prop :=
  ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ), ∀ G : Table k,
    ∃ x : RawProfile k, x.sizes = G.sizes ∧
      CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
      DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts) ε

end MultiNashRepair


