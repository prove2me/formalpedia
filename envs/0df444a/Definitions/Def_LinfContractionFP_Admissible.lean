-- Prove2me | Definitions.Def_LinfContractionFP_Admissible
-- name    : LinfContractionFP_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:07.274633+00:00
-- url     : https://prove2.me/theorems/124cdb0e-844f-4140-9bbf-1497deffcea1
-- title:
--   Admissible programs: only rational real constants
-- statement:
--   A program $P$ of the real RAM with an $f$-oracle is **admissible** if every real constant it loads (`const dst c`) is a rational number $c\in\mathbb Q$.
--
--   This is the uniform unit-cost real machine of the paper: it excludes programs that hide advice in an irrational machine constant. The algorithm of the paper needs only rational constants ($7/8$, $1/8$, $1/2$, $3/4$, $1/32$, $64$, …).
--
--   **Formalization Note** Restricting the programs makes an existence statement over admissible programs stronger than one over all programs. Pointer constants are integers by the core's design.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), footnote 6, p.19

import Mathlib
import Definitions.Def_LinfContractionFP_Machine

namespace LinfContractionFP

/-- A program is admissible if every real constant it loads is rational.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), footnote 6, p.19 ("a
unit-cost real machine").

**Formalization Note.** This is a reading of the unit-cost real machine that excludes encoding
advice in an irrational machine constant. It restricts the programs, so an existence claim over
admissible programs is stronger than one over all programs. The algorithm needs only rational
constants (`7/8`, `1/8`, `1/2`, `3/4`, `1/32`, `64`, …; the budgets can be tracked squared to
avoid `√3`). Pointer constants are integers by the core's design. -/
def Admissible (P : Program) : Prop :=
  ∀ ins ∈ P, ∀ (dst : ℕ) (c : ℝ), ins = Instr.core (.const dst c) → ∃ q : ℚ, c = q

end LinfContractionFP


