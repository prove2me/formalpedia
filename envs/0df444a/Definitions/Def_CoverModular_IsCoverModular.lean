-- Prove2me | Definitions.Def_CoverModular_IsCoverModular
-- name    : CoverModular_IsCoverModular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:28.197352+00:00
-- url     : https://prove2.me/theorems/ea78758a-0d2d-4fcf-a05e-98c4474908c3
-- title:
--   $\gamma$-cover modular set function (Definition 3)
-- statement:
--   Let $U$ be a universe set and $g:2^U\to\mathbb R$ a set function. The **marginal gain** of adding $i\in U$ to $S\subseteq U$ is $\rho_i(S)=g(S\cup\{i\})-g(S)$. For $\gamma\ge 1$, $g$ is **$\gamma$-cover modular** if for all $S,T\subseteq U$
--
--   $$
--   g(S\cup T)-\gamma\,g(S)\le\sum_{i\in T\setminus S}\rho_i(S).
--   $$
--
--   For $\gamma=1$ this is the characterization of submodularity in Definition 2 of the paper; for $\gamma>1$ it is a strict relaxation, in which $\gamma$ copies of $g(S)$ "cover" the effect of adding $T$ before marginal gains are counted.
--
--   **Formalization Note** Sets are finite subsets (`Finset U`); for a finite universe such as the arc set these are all subsets. The parameter range $\gamma\ge1$ is part of the definition.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3, Definition 3, p.9

import Mathlib

namespace CoverModular

/-- **γ-cover modularity** (DeValve, Pekeč, Wei, *Approximate submodularity in network design
problems*, SSRN 3844987, §3, Definition 3, p.9).

Given a universe `U` and a set function `g`, the marginal gain of adding `i` to `S` is
`ρ_i(S) = g(S ∪ {i}) − g(S)`. For `γ ≥ 1`, `g` is `γ`-cover modular if for all sets `S, T ⊆ U`
`g(S ∪ T) − γ g(S) ≤ ∑_{i ∈ T \ S} ρ_i(S)`.

**Formalization Note** Sets are `Finset U`; for the finite universes of the paper (the arc set
`𝓕`) these are all subsets. The parameter range `γ ≥ 1` of the definition's preamble is the
first conjunct. -/
def IsCoverModular {U : Type*} [DecidableEq U] (γ : ℝ) (g : Finset U → ℝ) : Prop :=
  1 ≤ γ ∧ ∀ S T : Finset U, g (S ∪ T) - γ * g S ≤ ∑ i ∈ T \ S, (g (insert i S) - g S)

end CoverModular


