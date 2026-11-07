-- Prove2me | Definitions.Def_QuantumHMMR_walkLaw
-- name    : QuantumHMMR_walkLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:17.036381+00:00
-- url     : https://prove2.me/theorems/f99deea1-38ba-4e2b-9191-209a034ea9de
-- title:
--   Iterated ensemble $\nu_n^{*T}$
-- statement:
--   The **iterated ensemble** $\nu_n^{*T}$ is the law of the product
--   $$
--   U_T U_{T-1} \cdots U_1, \qquad U_1, \dots, U_T \sim \nu_n \text{ independent},
--   $$
--   of $T$ independent updates of the walk; $\nu_n^{*0}$ is the point mass at the identity.
--
--   **Formalization Note** Built with the published `steps`, which places the newest factor on the left, as in the convention $\nu^{*r} \leftrightarrow U_r U_{r-1}\cdots U_1$ of p.10. The verification file proves it is a probability measure.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, p.10, and Theorem 1.3, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_stepLaw

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The iterated ensemble `ν_n^{*T}` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3 p.10 and Theorem 1.3, p.12): the law of the product
`U_T U_{T-1} ⋯ U_1` of `T` independent updates `U_k ∼ ν_n` (Eq. (8)).

**Formalization Note** The published `steps` composes independent samples with the newest factor on
the left (`steps μ (k+1) = convolve μ (steps μ k)`, the law of `U_{k+1} · (U_k ⋯ U_1)`), and
`steps μ 0` is the point mass at the identity. -/
noncomputable def walkLaw (G : Finset (Clifford.ProjectiveGroup 2)) (n m T : ℕ) : Measure (QMat n) :=
  steps (stepLaw G n m) T

end QuantumHMMR


