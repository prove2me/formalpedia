-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_IsLipSeminorm
-- name    : RouzeFranca_LearnGibbs_IsLipSeminorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:08.898035+00:00
-- url     : https://prove2.me/theorems/f046b3c8-9451-4880-8be3-28cc30f57b25
-- title:
--   Lipschitz constants on observables: nonnegative and absolutely homogeneous
-- statement:
--   A function $O\mapsto\|O\|_{\mathrm{Lip}}$ on operators on $n$ qubits is a **Lipschitz constant** in the sense used here if
--
--   1. $\|O\|_{\mathrm{Lip}}\ge 0$ for every $O$, and
--   2. $\|cO\|_{\mathrm{Lip}}=|c|\,\|O\|_{\mathrm{Lip}}$ for every real $c$.
--
--   Both Lipschitz constants of the paper, the quantum Hamming one $\|\cdot\|_{\mathrm{Lip},\square}$ of Eq. (34) and the differential one $\|\cdot\|_{\mathrm{Lip},\nabla}$ of Eq. (38), have these two properties; the paper writes $\|\cdot\|_{\mathrm{Lip}}$ for either. The main theorem is stated for every such function.
--
--   **Formalization Note** No triangle inequality and no finiteness condition is imposed; the theorems of the mission use only the two properties above.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Eq. (34), p. 21; Eq. (38), p. 22; §B.3, p. 25

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

namespace RouzeFranca.LearnGibbs

/-- A **Lipschitz constant** on observables: a nonnegative function `lip` on operators that is
absolutely homogeneous under real scalars, `‖cO‖_Lip = |c| ‖O‖_Lip`.

Rouzé, Stilck França, arXiv:2107.03333v4, Eq. (34), p. 21 (`‖O‖_Lip,□`), Eq. (38), p. 22
(`‖X‖_Lip,∇`), and p. 25 ("we simply write ∥.∥Lip and W1 to denote either of the Lipschitz
constants").

**Formalization Note.** This is the only structure of `‖·‖_Lip` the mission's statements use; both
`‖·‖_Lip,□` (34) and `‖·‖_Lip,∇` (38) satisfy it. No triangle inequality is required. -/
def IsLipSeminorm {n : ℕ} (lip : Mat n → ℝ) : Prop :=
  (∀ O, 0 ≤ lip O) ∧ ∀ (c : ℝ) (O : Mat n), lip ((c : ℂ) • O) = |c| * lip O

end RouzeFranca.LearnGibbs


