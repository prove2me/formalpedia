-- Prove2me | Definitions.Def_MantriCVQ_Pr
-- name    : MantriCVQ_Pr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:12.104344+00:00
-- url     : https://prove2.me/theorems/98f0d11d-e2d7-4c0c-8735-0eff238083f2
-- title:
--   Probability under a uniform seed
-- statement:
--   The probability of an event under the uniform distribution on a finite type: the number of outcomes in the event divided by the number of outcomes. The seeds of the random projections of §4.2 are sampled this way.
--
--   **Formalization Note** Every seed type used in this mission is nonempty.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.2, p. 17 (PDF p. 19)

import Mathlib

namespace MantriCVQ

open Classical in
/-- The probability of an event under the uniform distribution on a finite type: the seeds of the
random projections of §4.2 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.2, p. 17 (PDF
p. 19)) are sampled this way.

**Formalization Note** Every seed type used in this mission is nonempty, so the denominator is
positive. -/
noncomputable def Pr {α : Type} [Fintype α] (E : α → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / Fintype.card α

end MantriCVQ


