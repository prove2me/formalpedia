-- Prove2me | Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn
-- name    : RiskAverseConsistency_CompletelyContinuousOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:36.918809+00:00
-- url     : https://prove2.me/theorems/fd89843a-dbec-48af-b26d-8b3b73f6d051
-- title:
--   Completely continuous map
-- statement:
--   A map $G$ defined on a subset $S$ of a normed space $V$ is **completely continuous** if for every sequence $(v_k)\subset S$ and $v\in S$, $v_k\rightharpoonup v$ (weakly) implies $G(v_k)\to G(v)$.
--
--   The paper's notion for $G:V\to Y$ is the case $S=V$; Lemma 12 applies it to a map defined on $Z_{\mathrm{ad}}$. Compact linear operators on reflexive spaces, such as adjoints of compact Sobolev embeddings, are completely continuous.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.8; Lemma 12, p.9

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- A map `G` defined on a subset `S` of a normed space `V` is **completely continuous**: for every
sequence `(vₖ) ⊂ S` and `v ∈ S`, `vₖ ⇀ v` (weakly) implies `G(vₖ) → G(v)`.

Milz, Surowiec, arXiv:2207.14756v2, p.8 ("we refer to a mapping G : V → Y as completely
continuous if (vₖ) ⊂ V and vₖ ⇀ v ∈ V implies G(vₖ) → G(v)"); Lemma 12 (p.9) applies it to a
map defined on `Z_ad`.

Formalization Note: the paper's `G : V → Y` is the case `S = univ`. The codomain is any
topological space (the paper: a complete metric space). -/
def CompletelyContinuousOn {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace Y] (S : Set V) (G : V → Y) : Prop :=
  ∀ (u : ℕ → V) (v : V), (∀ k, u k ∈ S) → v ∈ S → WeakConv u v →
    Tendsto (fun k => G (u k)) atTop (𝓝 (G v))

end RiskAverseConsistency


