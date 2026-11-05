-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Atilde
-- name    : BauerleRiederMDP_PartialObs_Atilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:16.134745+00:00
-- url     : https://prove2.me/theorems/65190103-2154-4960-ad3d-552e1250160c
-- title:
--   The admissible fractions $\tilde A$ for power utility
-- statement:
--   For the power utility the admissible fractions of wealth invested in the stocks are
--   $$
--   \tilde A:=\{\alpha\in\mathbb R^d \mid 1+\alpha\cdot R(y)\ge0\ \text{a.s.}\}.
--   $$
--   Since by (FM) the support of $R(y)$ is independent of $y$, so is $\tilde A$.
--
--   **Formalization Note** The set is taken as the intersection over $y\in E_Y$; the condition is an almost sure inclusion in a closed half-space, which depends only on the support of $R(y)$, so under (FM)(ii) the sets for the different $y$ coincide.
-- source:
--   Bäuerle & Rieder (2011), §6.1 Power Utility, p.178 (PDF 191)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The admissible fractions `Ã` for power utility.**
Bäuerle & Rieder (2011), §6.1 "Power Utility", p.178 (PDF 191):
`Ã := {α ∈ ℝ^d | 1 + α · R(y) ≥ 0 IP-a.s.}`. "Since by Assumption (FM) the support of `R(y)` is
independent of `y`, the set `Ã` is independent of `y`."

**Formalization Note.** Lean takes the intersection over `y ∈ E_Y`; under (FM)(ii) the sets
`{α | 1 + α · R(y) ≥ 0 a.s.}` (an a.s. inclusion in a closed half-space, which depends only on the
support of `R(y)`) coincide for all `y`, so this is each of them. -/
def Atilde {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) : Set (Fin d → ℝ) :=
  {α | ∀ y, ∀ᵐ z ∂M.QR y, 0 ≤ 1 + α ⬝ᵥ z}

end BauerleRiederMDP.PartialObs


