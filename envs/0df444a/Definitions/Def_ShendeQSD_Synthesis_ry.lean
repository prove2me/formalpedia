-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_ry
-- name    : ShendeQSD_Synthesis_ry
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:30.457968+00:00
-- url     : https://prove2.me/theorems/ccc49562-729c-487b-bf3a-425a4e39172b
-- title:
--   The $y$-axis rotation $R_y(\theta)$ (the paper's sign convention)
-- statement:
--   For a real angle $\theta$, the **$y$-axis rotation** is the one-qubit gate
--
--   $$
--   R_y(\theta)=\begin{pmatrix} \cos\theta/2 & \sin\theta/2\\ -\sin\theta/2 & \cos\theta/2\end{pmatrix}.
--   $$
--
--   This is the convention printed in the paper. It is the transpose of the more common $e^{-i\theta\sigma_y/2}$, i.e. the common rotation by $-\theta$. Rotations compose additively, $R_y(a)R_y(b)=R_y(a+b)$. The central factor of the Cosine–Sine decomposition is a multiplexed $R_y$ gate.
--
--   **Formalization Note** Rows and columns are indexed by `Bool`, `false` $=|0\rangle$ first. The paper's sign is kept, because the statements of this mission (Theorems 4, 8, 10, 13, 14 and Appendix A.1) are written with it.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §2.2, p. 5

import Mathlib

namespace ShendeQSD.Synthesis

/-- **The y-axis rotation `R_y(θ)`.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§2.2, p. 5: "The y-axis rotation R_y(θ) = ( cos θ/2 sin θ/2 ; −sin θ/2 cos θ/2 )".

`ry θ = [[cos(θ/2), sin(θ/2)], [−sin(θ/2), cos(θ/2)]]`.

**Formalization Note.** A one-qubit matrix is indexed by `Bool`, `false` = `|0⟩` (first row and
column), `true` = `|1⟩`. This is the paper's sign convention (p. 5), which is the transpose of the
more common `exp(−iθY/2) = [[cos(θ/2), −sin(θ/2)], [sin(θ/2), cos(θ/2)]]`; equivalently
`ry θ` is the common rotation by `−θ`. -/
noncomputable def ry (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    match a, b with
    | false, false => ((Real.cos (θ / 2) : ℝ) : ℂ)
    | false, true => ((Real.sin (θ / 2) : ℝ) : ℂ)
    | true, false => ((-Real.sin (θ / 2) : ℝ) : ℂ)
    | true, true => ((Real.cos (θ / 2) : ℝ) : ℂ)

end ShendeQSD.Synthesis


