-- Prove2me | Definitions.Def_AutomorphicForm_ComplexIwasawa
-- name    : AutomorphicForm_ComplexIwasawa
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c9e20970-da75-5c40-a5a8-6d9587d34cbd
-- title:
--   Bottom-row coordinates and compact Iwasawa factor, 2×2 complex matrices
-- statement:
--   Fix a matrix $g \in M_2(\mathbb{C})$, with entries written $a = g_{00}$, $b = g_{01}$, $c = g_{10}$, $d = g_{11}$ in the `Fin 2` indexing, and let $z \in \mathbb{C}$. The module introduces four explicit coordinate functions attached to the pair $(g,z)$. First, `botP g z` is the complex number $P = a + zc$ and `botQ g z` is $Q = b + zd$; these are the two entries of the bottom row of the product $\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&z\\0&1\end{pmatrix} g$, that is, of $\begin{pmatrix} c & d \\ a+zc & b+zd\end{pmatrix}$. Second, `radC g z` is the non-negative real number $r = \sqrt{\lvert P\rvert^2 + \lvert Q\rvert^2}$, defined as `Real.sqrt` applied to the sum of the squared norms `Complex.normSq (botP g z)` and `Complex.normSq (botQ g z)`. Third, `kC g z` is the explicit $2\times2$ complex matrix
--   $$\begin{pmatrix} \overline{Q}/r & -\overline{P}/r \\ P/r & Q/r \end{pmatrix},$$
--   where each division is division in $\mathbb{C}$ by the coercion of the real number $r$. All four declarations are plain definitions: no non-degeneracy hypothesis on $g$ is imposed, and no property is asserted. In particular, nothing here claims that $r > 0$, that `kC g z` is unitary of determinant one, or that $\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&z\\0&1\end{pmatrix} g$ equals an upper-triangular matrix times `kC g z`; such facts, which require $\det g \neq 0$, are theorems elsewhere about these coordinates. Where $r = 0$ (possible only when $P = Q = 0$), division by zero in $\mathbb{C}$ returns $0$, so every entry of `kC g z` is then $0$ and the matrix is not unitary; statements using `kC` accordingly carry the hypotheses that force $r \neq 0$. The definitions are `noncomputable`, as are `Real.sqrt` and complex division.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients used (`Complex.normSq`, `Real.sqrt`, complex conjugation, the `!![…]` matrix notation) but no Iwasawa factorisation for $2\times2$ complex matrices; these coordinate functions are the project's own.
--
--   **Where it is used.** These coordinates package the Iwasawa decomposition of $GL_2(\mathbb{C})$ in the explicit form in which it is used on the automorphic side of the argument, the vector $(P,Q)$ and its norm $r$ recording the action on the relevant symmetric space and `kC g z` recording the compact factor. They are the common vocabulary of the modules establishing the factorisation identity, unitarity of the compact factor, and the attendant estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ComplexIwasawa.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ComplexConjugate

namespace AutomorphicForm.ComplexIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

def radC (z : ℂ) : ℝ := Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

end AutomorphicForm.ComplexIwasawa

end


