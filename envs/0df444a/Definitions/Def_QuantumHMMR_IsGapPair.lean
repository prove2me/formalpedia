-- Prove2me | Definitions.Def_QuantumHMMR_IsGapPair
-- name    : QuantumHMMR_IsGapPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:32.614249+00:00
-- url     : https://prove2.me/theorems/ce9c97bb-7582-4bb3-9f13-ae8e41e37e36
-- title:
--   Spectral-gap constants $(\gamma, a)$ of Lemma 4.2, Eqs. (13)–(14)
-- statement:
--   Fix the generating set $G$ and $t \ge 4$. Constants $\gamma, a > 0$ are **spectral-gap constants** when, for all sufficiently large $n$,
--   $$
--   \big\| M^{(t)}_{\chi_n} - M^{(t)}_{\mathcal C_n} \big\|_\infty \le 1 - \frac{\gamma}{n} \tag{13}
--   $$
--   and
--   $$
--   M^{(t)}_{\mathcal C_n}\big(I - M^{(t)}_{\xi_n}\big) M^{(t)}_{\mathcal C_n} \succeq a \big( M^{(t)}_{\mathcal C_n} - M^{(t)}_{\mu_H} \big). \tag{14}
--   $$
--   Here $\mathcal C_n$ is the uniform law on the $n$-qubit Clifford group modulo phase and $\mu_H$ the Haar measure. Lemma 4.2 provides such constants; the proof of Theorem 1.3 uses Lemma 4.2 only through them.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is the published `specNorm`; $\succeq$ is positive semidefiniteness of the difference. The finiteness of the Clifford group modulo phase is an instance argument.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.2, Eqs. (13), (14), p.13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_chiLaw
import Definitions.Def_QuantumHMMR_xiLaw

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45
open scoped ComplexOrder

namespace QuantumHMMR

/-- `γ, a > 0` are spectral-gap constants of Lemma 4.2 for the generating set `G` and the order `t`
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Eqs. (13), (14), p.13): for all sufficiently large `n`,
`‖M^{(t)}_{χ_n} - M^{(t)}_{C_n}‖_∞ ≤ 1 - γ/n` (13) and
`M^{(t)}_{C_n} (I - M^{(t)}_{ξ_n}) M^{(t)}_{C_n} ⪰ a (M^{(t)}_{C_n} - M^{(t)}_{μ_H})` (14).

The proof of Theorem 1.3 uses Lemma 4.2 only through these two constants; the milestones of the
proof take them as hypotheses in this form.

**Formalization Note** `M^{(t)}_ν` is the published `balancedUnitaryMoment ν t`; `C_n` is the uniform
law `cliffordLaw n` on the whole Clifford group modulo phase (its finiteness is supplied as an
instance argument), `μ_H` is `haarLaw n`; `‖·‖_∞` is the published `specNorm`; `⪰` is
`Matrix.PosSemidef` of the difference. -/
def IsGapPair [∀ n, Fintype (Clifford.ProjectiveGroup n)] (G : Finset (Clifford.ProjectiveGroup 2))
    (t : ℕ) (γ a : ℝ) : Prop :=
  0 < γ ∧ 0 < a ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    specNorm (balancedUnitaryMoment (chiLaw G n) t - balancedUnitaryMoment (cliffordLaw n) t)
      ≤ 1 - γ / n ∧
    (balancedUnitaryMoment (cliffordLaw n) t * (1 - balancedUnitaryMoment (xiLaw n) t) *
        balancedUnitaryMoment (cliffordLaw n) t -
      a • (balancedUnitaryMoment (cliffordLaw n) t - balancedUnitaryMoment (haarLaw n) t)).PosSemidef

end QuantumHMMR


