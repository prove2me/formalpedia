-- Prove2me | Definitions.Def_EPRPharma_Decision
-- name    : EPRPharma_Decision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:09.374103+00:00
-- url     : https://prove2.me/theorems/624af813-3a1a-4c45-8f90-cb70e0c755c7
-- title:
--   The producer's decision $(p,\eta_d,\eta_p)$
-- statement:
--   A decision of the pharmaceutical producer is a triple $(p,\eta_d,\eta_p)$ of real numbers: the unit price $p$ of the medicine, the promotional effort $\eta_d$ targeting the doctor and the promotional effort $\eta_p$ targeting the patient.
--
--   The bounds $0\le\eta_d,\eta_p\le 1$ and the doctor's participation are imposed by `DecisionFeasible`; the price is unrestricted (the paper notes that the optimal price may be negative).
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered)

import Mathlib

namespace EPRPharma

/-- **The producer's pricing and promotional decision (p, η_d, η_p).**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.2, p. 11 (unnumbered):
"the producer sets the unit price of the medicine p and the level of promotional efforts targeting
the doctor and patient, η_d and η_p, respectively".

**Formalization Note.** All three components are real numbers; the bounds 0 ≤ η_d, η_p ≤ 1 and the
doctor's participation are imposed by `DecisionFeasible`. The price is unrestricted (Online
Appendix p. 1: "we may have p* < 0"). -/
structure Decision where
  /-- p, the unit price of the medicine. -/
  p : ℝ
  /-- η_d, promotional effort targeting the doctor. -/
  etaD : ℝ
  /-- η_p, promotional effort targeting the patient. -/
  etaP : ℝ

end EPRPharma


