-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_ConservationDefects
-- name    : MultiwayGap2325_Main_Supplement_ConservationDefects
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:07:06.050993+00:00
-- url     : https://prove2.me/theorems/dad1d81a-5e1e-487c-a9f2-50b0d0eca81d
-- title:
--   Selected incoming-supply-minus-divergence integrals
-- statement:
--   For a realized non-opposite cut $C$ and face $S$, this module defines
--   $$
--   D_S(C)=\int_{\Omega_S}\left(b_{C(x)}(x)-\operatorname{div}F_{C(x)}(x)\right)dx,
--   $$
--   where $b_\ell$ is the sum of the incoming supplies from all parent faces, and the total $\sum_S D_S(C)$.
--
--   These are precisely the remaining terms after terminal and coordinate-facet contributions are grouped in Lemma 5.2. Conservation will subsequently bound each $D_S(C)$ below by the negative integrated allowance.
--
--   **Formalization Note** These are only integrated expressions. Their measurability and the conservation inequalities are separate theorem obligations.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), equation (15), p.14; supply convention (13), p.12.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

/-- On one face, the incoming supply selected by the cut minus its selected
interior divergence. -/
def conservationDefect {q : ℕ} (T : ℝ) (D : FlowData q) (S : Face q)
    (C : Simplex q → CutLabel q) : ℝ :=
  ∫ x, (incomingSupply D S (ambientCut C x) x -
    divergenceAt D S (ambientCut C x) x) ∂faceVolume T S

/-- The sum occurring on the right of the summation identity (15). -/
def totalConservationDefect {q : ℕ} (T : ℝ) (D : FlowData q)
    (C : Simplex q → CutLabel q) : ℝ :=
  ∑ S : Face q, conservationDefect T D S C

end MultiwayGap2325.Main.Supplement


