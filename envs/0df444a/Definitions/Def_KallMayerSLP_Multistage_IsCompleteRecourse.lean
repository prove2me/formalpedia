-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsCompleteRecourse
-- name    : KallMayerSLP_Multistage_IsCompleteRecourse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:59.609699+00:00
-- url     : https://prove2.me/theorems/b9824d7a-dd76-47ad-b7ab-2020fe124d10
-- title:
--   Complete recourse matrix
-- statement:
--   A matrix $W\in\mathbb R^{m\times n}$ is a **complete recourse matrix** if
--   $$
--   \{z\mid z=Wy,\ y\ge0\}=\mathbb R^{m}.
--   $$
--   Equivalently, the system $Wy=z$, $y\ge0$ is solvable for every right-hand side $z$. This is a condition on the matrix alone.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, §2, (2.6), p.201 (PDF 210)

import Mathlib

namespace KallMayerSLP.Multistage

open scoped Matrix

/-- `W` is a **complete recourse matrix**: `{z | z = W y, y ≥ 0} = ℝ^m` (Kall & Mayer, *Stochastic
Linear Programming* (2005), Chapter 3, (2.6), p.201, PDF 210). -/
def IsCompleteRecourse {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ z : Fin m → ℝ, ∃ y : Fin n → ℝ, 0 ≤ y ∧ W *ᵥ y = z

end KallMayerSLP.Multistage


