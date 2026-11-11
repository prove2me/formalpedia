-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_outState
-- name    : GapAgnosticGS_OracleAlg_outState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:32.265598+00:00
-- url     : https://prove2.me/theorems/bcf09c92-cb8d-479f-a89e-77b5fb1054b5
-- title:
--   Output state $\rho$: the reduced state of the output register
-- statement:
--   If a run halts at history $h$ with branch vector $\psi_h\ne0$, its **output state** is the reduced density matrix of the normalized branch vector on the output register $Y$:
--
--   $$\rho_{yy'}=\frac{1}{\|\psi_h\|^2}\sum_{q,c,k}\psi_h(q,y,c,k)\,\overline{\psi_h(q,y',c,k)} ,$$
--
--   with the oracle register, the control qubit and the workspace traced out without measurement. This is the state $\rho$ of Theorem 1.1 and the state $\rho_I$ of Problem 3.2 (the paper traces out the reference and work registers, App. A.7).
--
--   **Formalization Note** For a zero branch vector the value is the zero matrix; such histories have probability $0$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3); Problem 3.2, p.9 (PDF p.10); App. A.7, p.34 (PDF p.35)

import Definitions.Def_GapAgnosticGS_OracleAlg_branch

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3): "outputs … a state ρ"; Problem 3.2, p.9 (PDF p.10): "output
a state ρ_I on the input register I"; Appendix A.7, p.34 (PDF p.35): "Tracing out the reference
and work registers leaves a selector state". The output state of a run that ends at history `h`:
the reduced density matrix on the output register `Y` of the normalized branch vector,
`ρ_{y y'} = Σ_{q,c,k} ψ(q,y,c,k) conj(ψ(q,y',c,k)) / ‖ψ‖²` (the oracle register, the control
qubit and the workspace are traced out, unmeasured).

**Formalization Note.** For a zero branch vector the value is the zero matrix; such histories
have probability `0` and contribute nothing to `successProb`. -/
noncomputable def OracleAlg.outState {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) (h : List ℕ) : Matrix Y Y ℂ :=
  Matrix.of fun y y' => ((‖A.branch U h‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    ∑ q : Q, ∑ c : Bool, ∑ k : Fin (A.w h),
      A.branch U h (q, y, c, k) * star (A.branch U h (q, y', c, k))

end GapAgnosticGS


