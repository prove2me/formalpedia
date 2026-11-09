-- Prove2me | Definitions.Def_InflMaxAdapt_expInfluence
-- name    : InflMaxAdapt_expInfluence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:39.785112+00:00
-- url     : https://prove2.me/theorems/38810bab-264d-480e-ac9c-6b7711e0a373
-- title:
--   Expected influence $\mathbb E[\sigma(S)]$
-- statement:
--   The **expected influence** of a seed set $S \subseteq V$ is
--   $$
--   \mathbb E[\sigma(S)] \;=\; \sum_{A \subseteq V^2} \mathbb P(A)\, |C_A(S)| ,
--   $$
--   the expected number of vertices reached from $S$ when the live arcs are drawn from the independent cascade law.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_arcWeight
import Definitions.Def_InflMaxAdapt_arcCascade

namespace InflMaxAdapt

/-- The expected influence `E[σ(S)] = E|C(S)|` of a seed set `S` in the arc model
(Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), as the finite sum over live arc sets weighted by
their probability `arcWeight p A`. -/
noncomputable def expInfluence {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ A : Finset (V × V), arcWeight p A * ((arcCascade A S).card : ℝ)

end InflMaxAdapt


