-- Prove2me | Definitions.Def_ReplParity_massOutside
-- name    : ReplParity_massOutside
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:38.470423+00:00
-- url     : https://prove2.me/theorems/b8b7952d-e37a-4f57-8159-953106586c7e
-- title:
--   Mass outside a subspace, $Q(\mathbb F_2^n\setminus V)$
-- statement:
--   For a distribution $Q$ on $\mathbb F_2^n$ and a subspace $V$,
--   $$Q(\mathbb F_2^n\setminus V)=\sum_{v\notin V}Q(v).$$
--   This is the uncovered mass that Lemmas 3.2–3.3 and Propositions 3.4–3.5 control.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Lemma 3.2 (ii), p.15 (PDF p.17); Lemma 3.3, p.17; Propositions 3.4–3.5, pp.17–18

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

open Classical in
/-- **Mass outside a subspace, `Q(𝔽ⁿ₂ \ V)`.** Shen, Zhong, *Replicable Parity Learning: Cubic
Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Lemma 3.2 (ii), p.15 (PDF p.17), Lemma 3.3, p.17, Propositions 3.4–3.5, pp.17–18.

`massOutside Q V = Q(𝔽ⁿ₂ \ V) = ∑_{v ∉ V} Q(v)`. -/
noncomputable def massOutside {n : ℕ} (Q : PMF (Vec n)) (V : Subsp n) : ℝ :=
  ∑ v : Vec n, if v ∉ V then (Q v).toReal else 0

end ReplParity


