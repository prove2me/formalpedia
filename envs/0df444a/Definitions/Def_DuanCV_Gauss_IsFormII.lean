-- Prove2me | Definitions.Def_DuanCV_Gauss_IsFormII
-- name    : DuanCV_Gauss_IsFormII
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:42.523+00:00
-- url     : https://prove2.me/theorems/7b1f4ff6-8cc7-4b80-b3e0-75e870f50765
-- title:
--   A covariance in standard form II with parameters satisfying (11)
-- statement:
--   A real $4\times4$ matrix $V$ is **in standard form II** with parameters $n_i,m_i,c_i$ when $V=M_s^{II}$ and
--
--   $$(n_1-1)(m_2-1)=(n_2-1)(m_1-1),$$
--
--   $$|c_1|-|c_2|=\sqrt{(n_1-1)(m_1-1)}-\sqrt{(n_2-1)(m_2-1)},$$
--
--   with both radicands nonnegative.
--
--   These are the constraints that single out, among the local symplectic images of a covariance, the one to which Theorem 2 applies.
--
--   **Formalization Note** The paper prints the first constraint as a ratio, $\frac{n_1-1}{m_1-1}=\frac{n_2-1}{m_2-1}$. It is cross-multiplied here because the ratio is $0/0$ for a thermal state tensored with the vacuum, and the nonnegativity of the radicands is written out because Lean's square root of a negative number is $0$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eqs. (10)–(11), p. 3

import Mathlib
import Definitions.Def_DuanCV_Gauss_standardFormII

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace DuanCV.Gauss

/-- **`V` is in standard form II with parameters `nᵢ, mᵢ, cᵢ`.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eqs. (10)–(11), p. 3.

`V` equals the matrix (10), and the parameters satisfy (11a) and (11b), where the two radicands of
(11b) are nonnegative.

**Formalization Note.** (11a) is printed as `(n₁-1)/(m₁-1) = (n₂-1)/(m₂-1)`. It is cross-multiplied
here: the printed ratio is undefined for `ρ_th ⊗ |0⟩⟨0|`, and a Lean `0/0 = 0` would make it true by
accident. `Real.sqrt` of a negative number is `0` in Lean, so the nonnegativity of the radicands,
which the real square roots of (11b) presuppose, is written out. -/
def IsFormII (V : Cov 2) (n1 n2 m1 m2 c1 c2 : ℝ) : Prop :=
  V = standardFormII n1 n2 m1 m2 c1 c2 ∧
    (n1 - 1) * (m2 - 1) = (n2 - 1) * (m1 - 1) ∧
    0 ≤ (n1 - 1) * (m1 - 1) ∧ 0 ≤ (n2 - 1) * (m2 - 1) ∧
    |c1| - |c2| = Real.sqrt ((n1 - 1) * (m1 - 1)) - Real.sqrt ((n2 - 1) * (m2 - 1))

end DuanCV.Gauss


