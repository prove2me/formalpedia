-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_rz
-- name    : ShendeQSD_Synthesis_rz
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:30.712802+00:00
-- url     : https://prove2.me/theorems/d51b2e37-56e2-4722-8f97-c87ce8aaaa3b
-- title:
--   The $z$-axis rotation $R_z(\theta)$
-- statement:
--   For a real angle $\theta$, the **$z$-axis rotation** is the one-qubit gate
--
--   $$
--   R_z(\theta)=\begin{pmatrix} e^{-i\theta/2} & 0\\ 0 & e^{i\theta/2}\end{pmatrix}.
--   $$
--
--   It is one of the two rotation families from which the paper's multiplexed rotations are built; the multiplexed $R_z$ gates appear twice in the Quantum Shannon Decomposition.
--
--   **Formalization Note** A one-qubit matrix is indexed by `Bool`, with `false` standing for $|0\rangle$ (first row and column) and `true` for $|1\rangle$.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §2.2, p. 5

import Mathlib

namespace ShendeQSD.Synthesis

/-- **The z-axis rotation `R_z(θ)`.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§2.2, p. 5: "The z-axis rotation R_z(θ) = ( e^{−iθ/2} 0 ; 0 e^{iθ/2} )".

`rz θ = diag(e^{−iθ/2}, e^{iθ/2})`.

**Formalization Note.** A one-qubit matrix is indexed by `Bool`, `false` = `|0⟩` (first row and
column), `true` = `|1⟩`. -/
noncomputable def rz (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b =>
    if b then Complex.exp ((θ : ℂ) / 2 * Complex.I) else Complex.exp (-((θ : ℂ) / 2) * Complex.I)

end ShendeQSD.Synthesis


