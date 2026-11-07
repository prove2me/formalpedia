-- Prove2me | Definitions.Def_BrouwerLaplacian_centering
-- name    : BrouwerLaplacian_centering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:20.058292+00:00
-- url     : https://prove2.me/theorems/4e9c2c4e-1592-4760-a3d6-58e4a7b60c40
-- title:
--   All-ones matrix $J$ and centering matrix $C=I_n-\frac1nJ$
-- statement:
--   For $n\in\mathbb N$, let $J=\mathbf 1\mathbf 1^{\mathsf T}$ be the $n\times n$ real matrix all of whose entries equal $1$, and let
--
--   $$C=I_n-\frac1n J$$
--
--   be the **centering matrix**. For $n\ge 1$, $C$ is the orthogonal projection of $\mathbb R^n$ onto the hyperplane $\mathbf 1^{\perp}=\{x:\sum_i x_i=0\}$; it satisfies $C\mathbf 1=0$, and $Cx=x$ for $x\perp\mathbf 1$. The paper compares graph Laplacians with multiples of $C$ and conjugates matrices by $C$.
--
--   **Formalization Note** Matrices are indexed by $\mathrm{Fin}\,n=\{0,\dots,n-1\}$. At $n=0$ the matrix is empty, so the Lean convention $0^{-1}=0$ affects no entry.
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, §2 (Notation), p.2

import Mathlib

namespace BrouwerLaplacian

/-- **The all-ones matrix** `J = 𝟙𝟙ᵀ` of size `n × n`.
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §2 (Notation), p.2:
"Let J = 11ᵀ be the all ones matrix". -/
def onesMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => 1

/-- **The centering matrix** `C = Iₙ − (1/n) J`.
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §2 (Notation), p.2:
"Let J = 11ᵀ be the all ones matrix and C = Iₙ − 1/n J be the centering matrix."

**Formalization Note.** Real `n × n` matrices indexed by `Fin n` (the paper's `[n]` shifted to
`0, …, n−1`). At `n = 0` the matrix is empty, so the Lean convention `(0 : ℝ)⁻¹ = 0` changes
no entry. -/
noncomputable def centering (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (n : ℝ)⁻¹ • onesMat n

end BrouwerLaplacian


