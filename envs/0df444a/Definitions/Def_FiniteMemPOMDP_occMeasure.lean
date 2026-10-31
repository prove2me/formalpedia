-- Prove2me | Definitions.Def_FiniteMemPOMDP_occMeasure
-- name    : FiniteMemPOMDP_occMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:17.776211+00:00
-- url     : https://prove2.me/theorems/4bd2176e-00fa-4d77-9652-5a03f2b49c3d
-- title:
--   Occupation measure $z_m[p_1,\sigma]$
-- statement:
--   The **$m$-stage occupation measure** $z_m[p_1,\sigma]\in\Delta(\Delta(\mathcal K))$ is the law of the belief $P_m$ at stage $m$ when the initial belief is $p_1$ and $\sigma$ is played:
--
--   $$z_m[p_1,\sigma](C)=\mathbb P^{p_1}_\sigma(P_m\in C).$$
--
--   It is the sum, over the histories $h$ of length $m-1$, of $\mathbb P^{p_1}_\sigma(H_m=h)$ times the Dirac mass at the belief after $h$.
--
--   **Formalization Note** Only the Dirac initial distribution $\delta_{p_1}$ is needed. The stage index is shifted: $z_m$ is `occMeasure Γ p σ (m - 1)`.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition A.5, p.23

import Mathlib
import Definitions.Def_FiniteMemPOMDP_belief

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]
  [DecidableEq A] [DecidableEq S]

/-- **The occupation measure `z_m[p1, σ]`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition A.5, p.23: "Given a POMDP
Γ = (K, A, S, q, g), a measure µ ∈ ∆(∆(K)) and a strategy σ, consider the following dynamic over
∆(K). First, P1 is drawn according to µ. Then, (Pn)n≥1 is obtained by playing according to σ. …
We denote the m-stage occupation measure zm[µ, σ] ∈ ∆(∆(K)) by the law of Pm over ∆(K)." The paper
then identifies `p1` with `δ_{p1}` ("For sake of notation, we identify ∆(K) with the extreme points
of ∆(∆(K))").

`occMeasure Γ p σ n` is the law of the belief `P_{n+1}` at stage `n + 1` (after `n` recorded pairs)
when the initial belief is `p`: the sum over the histories `h` of length `n` of
`P^p_σ(H_{n+1} = h) δ_{P(h)}`, where `P(h) = belief Γ p σ h`.

**Formalization Note** Only the Dirac initial distribution `µ = δ_{p1}` is needed (Lemma A.8 uses
`z_m[p1, σ^ε]`). The stage index is shifted: `z_m` is `occMeasure Γ p σ (m − 1)`. -/
noncomputable def occMeasure (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (n : ℕ) : Measure (stdSimplex ℝ K) :=
  ∑ h : Fin n → A × S,
    (lawOfPlays Γ p σ {ω | historyAt n ω = List.ofFn h}) • Measure.dirac (belief Γ p σ (List.ofFn h))

end FiniteMemPOMDP


