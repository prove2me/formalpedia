-- Prove2me | Definitions.Def_DSSYKScales_defs
-- name    : DSSYKScales_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T01:46:35.720919+00:00
-- url     : https://prove2.me/theorems/5bbace99-4064-4818-9419-42de1701e94e
-- title:
--   DSSYK$_\infty$ (Susskind 2022): double-scaled limit, scrambling probability, Hamiltonian second moments
-- statement:
--   Shared definitions for the double-scaled SYK model at infinite temperature (DSSYK$_\infty$), following Susskind (2022).
--
--   1. **Double-scaled limit.** A sequence of models indexed by $n$, with $N_n$ Majorana fermions and interaction order $q_n$, is *double scaled with parameter* $\lambda$ if
--   $$\lambda>0,\qquad N_n\to\infty,\qquad \frac{q_n^2}{N_n}\to\lambda \quad (n\to\infty).$$
--   This is eq. (3.3), $q^2/N=\lambda$ with $\lambda$ fixed. It forces $q_n\to\infty$.
--
--   2. **Scrambling probability.** For $N,q$ and a coupling $\mathcal J$, the epidemic scrambling function in cosmic time $t$ is (eq. (8.1))
--   $$P_{N,q}(t)=1-\Bigl(1+\frac{q}{N}\,e^{(q-1)\mathcal J t}\Bigr)^{-\frac{1}{q-1}}.$$
--
--   3. **Second moment of the cosmic Hamiltonian.** $H_c=\sum_{|I|=q} j_I\,\chi_I$ (eq. (3.4)) has $\binom{N}{q}$ independent Gaussian couplings with variance $\langle jj\rangle = q!\,\mathcal J^2/N^{q-1}$. Its infinite-temperature second moment is the number of terms times the variance (eqs. (3.9), (11.1)):
--   $$\langle H_c^2\rangle_{N,q}=\binom{N}{q}\cdot\frac{q!}{N^{\,q-1}}\,\mathcal J^2 .$$
--
--   4. **Second moment of the string Hamiltonian.** Since $H_s=H_c/q$ (eq. (3.7)),
--   $$\langle H_s^2\rangle_{N,q}=\frac{\langle H_c^2\rangle_{N,q}}{q^2}.$$
--
--   These are the objects that every statement in this mission refers to.
--
--   **Formalization Note** $N$ and $q$ are natural numbers cast to reals. The exponent $-1/(q-1)$ is a real power of a base $\ge 1$. For $q=1$ it is $-1/0=0$ in Lean, and $N^{q-1}$ uses truncated subtraction. Both only affect finitely many terms of a double-scaled sequence, so no limit changes. The operator identity behind item 3 (the Wick contraction in the maximally mixed state, $\operatorname{tr}(\chi_I\chi_{I'})/\operatorname{tr}1=\delta_{II'}$) is not formalized. Item 3 records its result as a definition.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, eqs. (3.3), (3.4), (3.7), (3.9), (8.1), (11.1), (11.2)

import Mathlib

namespace DSSYKScales

open Filter Topology

/-- The double-scaled limit of SYK (Susskind 2022, eq. (3.3)): a sequence of models
indexed by `n`, with `N n` fermions and interaction order `q n`, such that `N n → ∞`
and `(q n)^2 / N n → lam`, where the fixed parameter `lam` is strictly positive. -/
def IsDoubleScaledLimit (N q : ℕ → ℕ) (lam : ℝ) : Prop :=
  0 < lam ∧
  Tendsto (fun n => (N n : ℝ)) atTop atTop ∧
  Tendsto (fun n => ((q n : ℝ) ^ 2) / (N n : ℝ)) atTop (𝓝 lam)

/-- The "epidemic" scrambling probability of DSSYK∞ as a function of cosmic time `t`
(Susskind 2022, eq. (8.1)):
`P(t) = 1 - (1 + (q/N) * exp((q - 1) J t)) ^ (-1/(q - 1))`. -/
noncomputable def scramblingProbability (N q : ℕ) (J t : ℝ) : ℝ :=
  1 - (1 + (q : ℝ) / (N : ℝ) * Real.exp (((q : ℝ) - 1) * J * t)) ^ (-1 / ((q : ℝ) - 1))

/-- Infinite-temperature second moment `⟨H_c^2⟩` of the cosmic Hamiltonian (3.4):
the number `C(N, q)` of `q`-fold couplings times the coupling variance
`⟨j j⟩ = q! J^2 / N^(q-1)` (Susskind 2022, eqs. (3.4), (3.9), (11.1)). -/
noncomputable def cosmicHamiltonianSecondMoment (N q : ℕ) (J : ℝ) : ℝ :=
  (N.choose q : ℝ) * ((q.factorial : ℝ) / (N : ℝ) ^ (q - 1) * J ^ 2)

/-- Infinite-temperature second moment `⟨H_s^2⟩` of the string-unit Hamiltonian
`H_s = H_c / q` (Susskind 2022, eqs. (3.7), (11.2)). -/
noncomputable def stringHamiltonianSecondMoment (N q : ℕ) (J : ℝ) : ℝ :=
  cosmicHamiltonianSecondMoment N q J / (q : ℝ) ^ 2

end DSSYKScales


