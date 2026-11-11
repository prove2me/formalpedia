-- Prove2me | Definitions.Def_QMultiMean_gridPoint
-- name    : QMultiMean_gridPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:09.093852+00:00
-- url     : https://prove2.me/theorems/00c7314e-4239-4123-a793-62e53c23b2f5
-- title:
--   The grid $G=\{j/m-1/2+1/(2m)\}^d$ and the uniform distribution on it
-- statement:
--   For a positive integer $m$, the **grid**
--   $$G=\Big\{\frac jm-\frac12+\frac1{2m}:j\in\{0,\dots,m-1\}\Big\}^d\subset(-1/2,1/2)^d$$
--   has $m^d$ points, indexed by $j\in\{0,\dots,m-1\}^d$. The probability of an event under $u\sim G$, the uniform distribution on $G$, is the number of grid points in the event divided by $m^d$.
--
--   The grid indexes the directions $u$ of the directional mean oracle (Proposition 3.2) and the basis of the register $\mathcal H_G$ to which Algorithm 1 applies the quantum Fourier transform.
--
--   **Formalization Note** The index set is `Fin d → Fin m`, which also indexes the basis of $\mathcal H_G$.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.9, start of §3.1

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean

/-- The point of the grid
`G = {j/m − 1/2 + 1/(2m) : j ∈ {0, …, m − 1}}^d ⊂ (−1/2, 1/2)^d`
(Cornelissen, Hamoudi, Jerbi, arXiv:2111.09787v2, p.9) with index `j : Fin d → Fin m`.

**Formalization Note.** `G` is indexed by `Fin d → Fin m`, a set of `m^d` labels in bijection with
`G` for `m ≥ 1`; these labels also index the standard basis of `H_G`. -/
noncomputable def gridPoint {d : ℕ} (m : ℕ) (j : Fin d → Fin m) : Vec d :=
  WithLp.toLp 2 (fun i => ((j i : ℕ) : ℝ) / m - 1 / 2 + 1 / (2 * (m : ℝ)))

open Classical in
/-- The probability `Pr_{u∼G}[A(u)] = #{u ∈ G : A(u)} / m^d` of an event under the uniform
distribution on the grid `G` (arXiv:2111.09787v2, p.9). -/
noncomputable def gridProb (d m : ℕ) (A : (Fin d → Fin m) → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / (m : ℝ) ^ d

end QMultiMean


