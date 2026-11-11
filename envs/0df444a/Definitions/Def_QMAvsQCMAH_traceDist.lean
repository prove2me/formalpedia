-- Prove2me | Definitions.Def_QMAvsQCMAH_traceDist
-- name    : QMAvsQCMAH_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:25.125488+00:00
-- url     : https://prove2.me/theorems/f5270498-1c67-42ff-ae38-13d14a3e8403
-- title:
--   Trace distance
-- statement:
--   The **trace distance** of two density operators $\rho,\sigma$ is
--   $$\tfrac12\|\rho-\sigma\|_1=\max_{0\le P\le I}\operatorname{Re}\operatorname{tr}\bigl(P(\rho-\sigma)\bigr),$$
--   written here in its variational form (Helstrom).
--
--   **Formalization Note.** The definition takes the supremum over all operators $0\le P\le I$, which for density operators equals half the trace norm of the difference.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18; Lemma 5, p.22; Lemma 7(3), p.28

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

open ComplexOrder
/-- The **trace distance** `½‖ρ − σ‖₁` of two density operators, in its variational form
`max_{0 ≤ P ≤ I} Re tr(P(ρ − σ))`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18 (PDF p.21): trace distance of states; Lemma 5, p.22 (PDF p.25):
"½‖A^O − A^{O′}‖₁"; Lemma 7(3), p.28: "to trace-distance error ϵ".

**Formalization Note.** For two density operators (equal trace) the supremum over operators
`0 ≤ P ≤ I` equals `½‖ρ − σ‖₁` (Helstrom); the set is nonempty (`P = 0`) and bounded. -/
noncomputable def traceDist {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  sSup {x : ℝ | ∃ P : Matrix ι ι ℂ, P.PosSemidef ∧ (1 - P).PosSemidef ∧
    x = ((P * (ρ - σ)).trace).re}

end QMAvsQCMAH


