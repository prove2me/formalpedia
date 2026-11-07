-- Prove2me | Definitions.Def_QuantumHMMR_advantage
-- name    : QuantumHMMR_advantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:22.303405+00:00
-- url     : https://prove2.me/theorems/9a166f7d-7dbc-4a6b-aa0f-9646a2fc50a8
-- title:
--   Adaptive distinguishing advantage $\delta_t(\nu, \mu)$, Eq. (6)
-- statement:
--   For two ensembles $\nu, \mu$ of $n$-qubit unitaries, the **adaptive $t$-query advantage** is
--   $$
--   \delta_t(\nu, \mu) = \sup_{A, M_A} \Big| \mathop{\mathbb E}_{U \sim \nu} \mathrm{Tr}\big[M_A |A^U_t\rangle\langle A^U_t|\big] - \mathop{\mathbb E}_{U \sim \mu} \mathrm{Tr}\big[M_A |A^U_t\rangle\langle A^U_t|\big] \Big|, \tag{6}
--   $$
--   the supremum over all $t$-query algorithms (any number of ancillas) and all two-outcome measurements $(M_A, I - M_A)$. By Definition 3.1, $\nu$ is an $\epsilon$-approximate adaptive unitary $t$-design when $\delta_t(\nu, \mu_H) \le \epsilon$, $\mu_H$ the Haar measure.
--
--   **Formalization Note** The value lies in $[0, \infty]$ (a supremum of `ENNReal.ofReal` of the absolute differences), so it is never a junk value. Measurements are effects $0 \preceq M \preceq I$ (published `IsEffect`). Expectations are Bochner integrals; for the laws of this mission (probability measures supported on unitaries) the integrand is continuous and bounded on the support, hence integrable.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Definition 3.1, Eq. (6), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_acceptProb

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped ENNReal

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The adaptive `t`-query distinguishing advantage `δ_t(ν, μ)` of Definition 3.1, Eq. (6)
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.10):
`δ_t(ν, μ) = sup_{A, M_A} | E_{U∼ν} Tr[M_A |A^U_t⟩⟨A^U_t|] - E_{U∼μ} Tr[M_A |A^U_t⟩⟨A^U_t|] |`,
the supremum over every `t`-query algorithm (every ancilla count and every choice of `A_0, …, A_t`)
and every two-outcome measurement `(M_A, I - M_A)`. An ensemble `ν` is an `ε`-approximate adaptive
unitary `t`-design when `δ_t(ν, μ_H) ≤ ε`.

**Formalization Note** The value is in `ℝ≥0∞` (a supremum of `ENNReal.ofReal |…|`), so the
supremum is never a junk value. The measurement is any effect `0 ⪯ M ⪯ I` (published `IsEffect`).
Expectations are Bochner integrals; for the laws used in this mission (probability measures
supported on unitaries) the integrand is continuous and bounded on the support, hence integrable. -/
noncomputable def advantage {n : ℕ} (t : ℕ) (ν μ : Measure (QMat n)) : ℝ≥0∞ :=
  ⨆ (alg : AdaptiveAlg n t) (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ)
    (_ : IsEffect M),
    ENNReal.ofReal |∫ U, acceptProb alg M U ∂ν - ∫ U, acceptProb alg M U ∂μ|

end QuantumHMMR


