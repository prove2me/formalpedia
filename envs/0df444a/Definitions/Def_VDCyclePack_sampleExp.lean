-- Prove2me | Definitions.Def_VDCyclePack_sampleExp
-- name    : VDCyclePack_sampleExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:57.793299+00:00
-- url     : https://prove2.me/theorems/61ba80f0-0006-468d-8b35-a02e1e793f9a
-- title:
--   Expectation over the random subfamily of Lemma 5.1
-- statement:
--   For the random subfamily $Q\subseteq R$ of Lemma 5.1 and a function $f$ of subfamilies,
--   $$
--   \mathbb E[f(Q)]=\sum_{Q\subseteq R}\Pr[\text{sample}=Q]\,f(Q).
--   $$
--   Lemma 5.1 applies it to $f(Q)=\beta(\bigcup_{C\in Q}C)$.
--
--   **Formalization Note** A finite sum over the subsets of $R$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 5.1, p.15

import Mathlib
import Definitions.Def_VDCyclePack_sampleProb

namespace VDCyclePack

/-- **Expectation over the random subfamily of Lemma 5.1.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 5.1, p.15: "let Q be obtained by including each C ∈ R independently with
probability x_C/2 ... E[β(U)]".

`sampleExp R x f = Σ_{Q ⊆ R} sampleProb R x Q · f Q`, the expectation of `f(Q)` when each member
`C` of `R` is included independently with probability `x C / 2`.

**Formalization Note.** A finite sum over `R.powerset` with the product weights `sampleProb`. -/
noncomputable def sampleExp {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph)
    (x : G.Subgraph → ℝ) (f : Finset G.Subgraph → ℝ) : ℝ :=
  ∑ Q ∈ R.powerset, sampleProb R x Q * f Q

end VDCyclePack


