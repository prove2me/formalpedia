-- Prove2me | Definitions.Def_TensorNP_Rank_Construction
-- name    : TensorNP_Rank_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:57.06746+00:00
-- url     : https://prove2.me/theorems/acd2e6b7-30e3-4ff3-a4bf-51dc689642f1
-- title:
--   Proof of Theorem 1.14 and (30), p. 0:26 — the tensor A ∈ ℚ^{2×2×2} and the system (30)
-- statement:
--   Let $\mathbf x = [1,0]^\top$ and $\mathbf y = [0,1]^\top$ in $\mathbb Q^2$. The tensor of the proof of Theorem 1.14 is
--   $$
--   \mathcal A = 2\,\mathbf x\otimes\mathbf x\otimes\mathbf x - 4\,\mathbf y\otimes\mathbf y\otimes\mathbf x + 4\,\mathbf y\otimes\mathbf x\otimes\mathbf y - 4\,\mathbf x\otimes\mathbf y\otimes\mathbf y \in \mathbb Q^{2\times2\times2},
--   $$
--   that is, $a_{111} = 2$, $a_{221} = -4$, $a_{212} = 4$, $a_{122} = -4$, and all other entries are $0$.
--
--   The system (30) of Lemma 8.1 consists of the eight equations, in twelve unknowns $a_1,a_2,a_3,b_1,b_2,b_3,c_1,c_2,c_3,d_1,d_2,d_3$,
--   $$
--   \begin{aligned}
--   &a_1a_2a_3 + c_1c_2c_3 = 2, && a_1a_3b_2 + c_1c_3d_2 = 0, && a_2a_3b_1 + c_2c_3d_1 = 0, && a_3b_1b_2 + c_3d_1d_2 = -4,\\
--   &a_1a_2b_3 + c_1c_2d_3 = 0, && a_1b_2b_3 + c_1d_2d_3 = -4, && a_2b_1b_3 + c_2d_3d_1 = 4, && b_1b_2b_3 + d_1d_2d_3 = 0,
--   \end{aligned}
--   $$
--   stated over an arbitrary commutative ring. With $\mathbf u_i = [a_i,b_i]^\top$ and $\mathbf v_i = [c_i,d_i]^\top$, these are the eight entries of $\mathcal A = \mathbf u_1\otimes\mathbf u_2\otimes\mathbf u_3 + \mathbf v_1\otimes\mathbf v_2\otimes\mathbf v_3$.
--
--   These two objects carry the whole proof of Theorem 1.14: $\mathcal A$ is the example, and (30) is what a rational decomposition of $\mathcal A$ with two terms would have to satisfy.
--
--   **Formalization Note** Indices are 0-based in Lean: `tensorA 0 0 0 = 2`, `tensorA 1 1 0 = -4`, `tensorA 1 0 1 = 4`, `tensorA 0 1 1 = -4`. The equations of `System30` are in the printed order, including the printed factor order $c_2d_3d_1$ of the seventh.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, proof of Theorem 1.14 and Lemma 8.1, (30)

import Mathlib
import Definitions.Def_TensorNP_Rank_Defs

namespace TensorNP.Rank

/-- The vector `x = [1, 0]^⊤` of the proof of Theorem 1.14 (Hillar–Lim p. 0:26). -/
def vecX : Fin 2 → ℚ := ![1, 0]

/-- The vector `y = [0, 1]^⊤` of the proof of Theorem 1.14 (Hillar–Lim p. 0:26). -/
def vecY : Fin 2 → ℚ := ![0, 1]

/-- The rational tensor of the proof of Theorem 1.14 (Hillar–Lim p. 0:26):
`A = 2 x⊗x⊗x − 4 y⊗y⊗x + 4 y⊗x⊗y − 4 x⊗y⊗y ∈ ℚ^{2×2×2}`. With 0-based indices its nonzero
entries are `A 0 0 0 = 2`, `A 1 1 0 = -4`, `A 1 0 1 = 4`, `A 0 1 1 = -4`. -/
def tensorA : Fin 2 → Fin 2 → Fin 2 → ℚ :=
  (2 : ℚ) • outer vecX vecX vecX - (4 : ℚ) • outer vecY vecY vecX
    + (4 : ℚ) • outer vecY vecX vecY - (4 : ℚ) • outer vecX vecY vecY

/-- The system (30) of Hillar–Lim (Lemma 8.1, p. 0:26) of 8 polynomial equations in the 12
unknowns `a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃` over a commutative ring `K`, in the printed order. -/
def System30 {K : Type*} [CommRing K]
    (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : K) : Prop :=
  a₁ * a₂ * a₃ + c₁ * c₂ * c₃ = 2 ∧ a₁ * a₃ * b₂ + c₁ * c₃ * d₂ = 0 ∧
  a₂ * a₃ * b₁ + c₂ * c₃ * d₁ = 0 ∧ a₃ * b₁ * b₂ + c₃ * d₁ * d₂ = -4 ∧
  a₁ * a₂ * b₃ + c₁ * c₂ * d₃ = 0 ∧ a₁ * b₂ * b₃ + c₁ * d₂ * d₃ = -4 ∧
  a₂ * b₁ * b₃ + c₂ * d₃ * d₁ = 4 ∧ b₁ * b₂ * b₃ + d₁ * d₂ * d₃ = 0

end TensorNP.Rank


