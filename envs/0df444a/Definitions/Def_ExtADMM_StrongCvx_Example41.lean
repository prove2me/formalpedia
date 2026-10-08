-- Prove2me | Definitions.Def_ExtADMM_StrongCvx_Example41
-- name    : ExtADMM_StrongCvx_Example41
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:30.772433+00:00
-- url     : https://prove2.me/theorems/0899ecf7-4c5c-4d2d-803d-fa35e67a82bf
-- title:
--   (4.1), p. 14 — the strongly convex three-variable instance, its state vector and the iteration matrix of (1.5) at β = 1
-- statement:
--   **The instance (4.1).** Let $A_1=(1,1,1)^T$, $A_2=(1,1,2)^T$, $A_3=(1,2,2)^T$ be the columns of
--
--   $$A=\begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix},$$
--
--   and consider the strongly convex problem in three scalar variables
--
--   $$\min\ 0.05x_1^2+0.05x_2^2+0.05x_3^2\quad\text{s.t.}\quad A_1x_1+A_2x_2+A_3x_3=0 .$$
--
--   It is the special case of the three-block problem (1.1) with $n_1=n_2=n_3=1$, $p=3$, $\theta_i(x)=0.05x^2$, $b=0$ and $\mathcal X_i=\mathbb R$. Its unique solution is $x_1=x_2=x_3=0$.
--
--   **State vector.** For the direct extension of ADMM with $\beta=1$, the state after an iteration is $z=(x_2,x_3,\lambda_1,\lambda_2,\lambda_3)\in\mathbb R^5$.
--
--   **Iteration matrix.** $M_{41}$ is the $5\times5$ real matrix
--
--   $$M_{41}=\frac{1}{172081}\begin{pmatrix}145600&-15470&-8190&-8190&20020\\10000&164400&-5290&13620&-8080\\66440&128620&130051&-60940&-67450\\56440&-35780&-36740&97521&-59370\\-89160&-20310&-28550&-66370&92691\end{pmatrix}.$$
--
--   The paper does not print this matrix: it says only that each iteration of (1.5) on (4.1) "remains a fixed matrix mapping". $M_{41}$ was computed for this mission in exact rational arithmetic, by writing the first-order optimality conditions of the three subproblems of (1.5) at $\beta=1$ (the method of (3.2)–(3.9), pp. 10–11, with the gradients $0.1x_i$ of $\theta_i$ added) and solving for the new state. Its correctness is the content of the milestone *fixed matrix mapping*; a wrong entry makes that milestone false.
--
--   **Formalization Note** Scalars are `Fin 1 → ℝ`, each $A_i$ is a $3\times1$ matrix built by `col`, and the constant $0.05$ is the real literal `0.05`. The state's components are 0-based: $\lambda_1,\lambda_2,\lambda_3$ are `lam 0`, `lam 1`, `lam 2`. At $\beta=1$ the paper's scaled multiplier $\mu=\lambda/\beta$ of (3.8) equals $\lambda$, so no scaling appears.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, (4.1); state vector as in (3.8), p. 11

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_Diverge_Setting

namespace ExtADMM.StrongCvx

open Matrix

/-- The strongly convex instance (4.1), p. 14:
`min 0.05x₁² + 0.05x₂² + 0.05x₃²` s.t. `A₁x₁ + A₂x₂ + A₃x₃ = 0`, where `A₁ = (1,1,1)ᵀ`,
`A₂ = (1,1,2)ᵀ`, `A₃ = (1,2,2)ᵀ` are the columns of the matrix `[[1,1,1],[1,1,2],[1,2,2]]`
of (4.1), `xᵢ ∈ ℝ` (here `Fin 1 → ℝ`), `𝒳ᵢ = ℝ` and `b = 0`. -/
noncomputable def example41 : Problem 1 1 1 3 where
  A1 := ExtADMM.Diverge.col ![1, 1, 1]
  A2 := ExtADMM.Diverge.col ![1, 1, 2]
  A3 := ExtADMM.Diverge.col ![1, 2, 2]
  b := 0
  θ1 := fun x => (0.05 : ℝ) * x 0 ^ 2
  θ2 := fun x => (0.05 : ℝ) * x 0 ^ 2
  θ3 := fun x => (0.05 : ℝ) * x 0 ^ 2
  X1 := Set.univ
  X2 := Set.univ
  X3 := Set.univ

/-- The state `z = (x₂, x₃, λ₁, λ₂, λ₃)` of the direct extension of ADMM on (4.1) at `β = 1`
(the coordinates of (3.8) with `μ = λ/β = λ`). Components are 0-based: `λ₁, λ₂, λ₃` are
`lam 0, lam 1, lam 2`. -/
def stateVec (x2 x3 : Fin 1 → ℝ) (lam : Fin 3 → ℝ) : Fin 5 → ℝ :=
  ![x2 0, x3 0, lam 0, lam 1, lam 2]

/-- The iteration matrix of (1.5) with `β = 1` on (4.1), acting on `stateVec`. It is not
printed in the paper (p. 14 says only that each iteration "remains a fixed matrix mapping");
it was computed for this mission in exact rational arithmetic by the method of (3.2)–(3.9),
pp. 10–11, with the gradients `0.1xᵢ` of `θᵢ` added. `172081 = 1891 · 91`. -/
noncomputable def M41 : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 172081 : ℝ) •
  !![145600, -15470, -8190, -8190, 20020;
     10000, 164400, -5290, 13620, -8080;
     66440, 128620, 130051, -60940, -67450;
     56440, -35780, -36740, 97521, -59370;
     -89160, -20310, -28550, -66370, 92691]

end ExtADMM.StrongCvx


