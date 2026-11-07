-- Prove2me | Definitions.Def_StableVotingDistortion_voterMean
-- name    : StableVotingDistortion_voterMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:54.698268+00:00
-- url     : https://prove2.me/theorems/afdc01da-4fd4-4228-86c5-870ccc2aa636
-- title:
--   Expectation over a uniformly random voter
-- statement:
--   For a finite set $V$ of voters and $f:V\to\mathbb R$,
--   $$\mathbb E_{v\sim V}[f(v)]=\frac1{|V|}\sum_{v\in V}f(v).$$
--
--   Every per-voter quantity of this mission is averaged this way.
--
--   **Formalization Note** With no voters the value is $0$; the mission's theorems assume $V$ nonempty.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.5

import Mathlib

set_option autoImplicit false

namespace StableVotingDistortion

/-- The expectation over a uniformly random voter, `E_{v ∼ V}[f v] = (1/n) ∑_v f v`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §2, p.5: "We use v ∼ V to denote sampling a voter uniformly at random".

**Formalization Note.** With no voters this is `0`; every theorem of the mission assumes
`[Nonempty V]`. -/
noncomputable def voterMean {V : Type} [Fintype V] (f : V → ℝ) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ * ∑ v, f v

end StableVotingDistortion


