-- Prove2me | Definitions.Def_QubitPhaseEst_sgSeed
-- name    : QubitPhaseEst_sgSeed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:19:48.11119+00:00
-- url     : https://prove2.me/theorems/86e7a8f1-59f4-46d0-bb38-2a90f9f3f6f7
-- title:
--   Compensating phases and the Susskind–Glogower seed $\xi=\sum_{j,\alpha}|e(j,\alpha)\rangle\langle e(j,\alpha)|$
-- statement:
--   Fix a standard basis $|m,j\alpha\rangle$ and a state $R$. Real phases $\gamma(m,j\alpha)$ are **compensating** for $R$ when, for every block $(j,\alpha)$ and every $m<j$,
--
--   $$
--   e^{i(\gamma(m,j\alpha)-\gamma(m+1,j\alpha))}\,\langle m+1,j\alpha|R|m,j\alpha\rangle=\bigl|\langle m+1,j\alpha|R|m,j\alpha\rangle\bigr|.
--   $$
--
--   Given phases $\gamma$, the **generalized Susskind–Glogower vectors** are
--
--   $$
--   |e(j,\alpha)\rangle=\sum_{m=-j}^{j}e^{i\gamma(m,j\alpha)}|m,j,\alpha\rangle,
--   $$
--
--   and the **Susskind–Glogower seed** is $\xi=\sum_{j,\alpha}|e(j,\alpha)\rangle\langle e(j,\alpha)|$, Eqs. (19)–(20).
--
--   With compensating phases the matrix elements $\langle m,j\alpha|\xi|m+1,j\alpha\rangle$ cancel the phases of $\langle m+1,j\alpha|R|m,j\alpha\rangle$; this is how the seed attains the bound (16).
--
--   **Formalization Note** The compensation condition is the paper's p. 3 sentence ("in such a way that they compensate the corresponding phases"), written multiplicatively, so that a vanishing matrix element imposes nothing. The printed Eq. (18) has the same content when $R$ is real (no $y$ component of the Bloch vector) and the opposite sign otherwise.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 3, before Eq. (17) (compensating phases), Eqs. (19)–(20)

import Mathlib
import Definitions.Def_QubitPhaseEst_IsStandardBasis

open scoped Matrix

namespace QubitPhaseEst

/-- **Compensating phases.** arXiv:quant-ph/0411133v3, Sec. II, p. 3, before Eq. (17): the phases of
`⟨m, jα|ξ|m+1, jα⟩` "compensate the corresponding phases of `⟨m+1, jα|R_n|m, jα⟩`", i.e.
`e^{i(γ(m,jα) − γ(m+1,jα))} ⟨m+1, jα|R|m, jα⟩ = |⟨m+1, jα|R|m, jα⟩|` for every adjacent pair.

**Formalization Note.** This is the p. 3 prose, written multiplicatively, so that a vanishing matrix
element imposes nothing and no `Complex.arg` occurs. The printed Eq. (18), `χ = γ(m) − γ(m+1)`,
agrees with it for the paper's real `R` and has the opposite sign for general Bloch vectors
(a reading, not a change of the objects). -/
def IsCompensating {N : ℕ} (b : SpinIdx N → Qb N → ℂ) (R : Matrix (Qb N) (Qb N) ℂ)
    (γ : SpinIdx N → ℝ) : Prop :=
  ∀ (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) (i : Fin (N - 2 * (k : ℕ))),
    Complex.exp (((γ (spinBot k α i) : ℂ) - (γ (spinTop k α i) : ℂ)) * Complex.I) *
        braket (b (spinTop k α i)) R (b (spinBot k α i)) =
      (‖braket (b (spinTop k α i)) R (b (spinBot k α i))‖ : ℂ)

/-- **The generalized Susskind–Glogower vector** `|e(j, α)⟩ = Σ_m e^{iγ(m,jα)}|m, j, α⟩`,
arXiv:quant-ph/0411133v3, Sec. II, Eq. (20), p. 3. -/
noncomputable def sgVector {N : ℕ} (b : SpinIdx N → Qb N → ℂ) (γ : SpinIdx N → ℝ)
    (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) : Qb N → ℂ :=
  ∑ i, Complex.exp ((γ ⟨k, (i, α)⟩ : ℂ) * Complex.I) • b ⟨k, (i, α)⟩

/-- **The Susskind–Glogower seed** `ξ = Σ_{j,α} |e(j, α)⟩⟨e(j, α)|`, arXiv:quant-ph/0411133v3, Sec. II,
Eq. (19), p. 3. -/
noncomputable def sgSeed {N : ℕ} (b : SpinIdx N → Qb N → ℂ) (γ : SpinIdx N → ℝ) :
    Matrix (Qb N) (Qb N) ℂ :=
  ∑ k, ∑ α, Matrix.vecMulVec (sgVector b γ k α) (star (sgVector b γ k α))

end QubitPhaseEst


