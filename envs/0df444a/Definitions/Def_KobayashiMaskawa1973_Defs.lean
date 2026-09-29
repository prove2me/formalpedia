-- Prove2me | Definitions.Def_KobayashiMaskawa1973_Defs
-- name    : KobayashiMaskawa1973_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T17:51:49.314406+00:00
-- url     : https://prove2.me/theorems/09a8f5c7-e729-4ba9-a8a2-bba62c5065af
-- title:
--   Mixing matrices and rephasing freedom (Kobayashi--Maskawa 1973)
-- statement:
--   This file fixes the linear-algebraic model used throughout the mission: the mixing matrix of the charged weak current and the freedom to redefine the phases of the quark fields.
--
--   **Phase matrices.** For real numbers $a_1,\dots,a_n$, write
--   $$D(a)=\operatorname{diag}\!\left(e^{i a_1},\dots,e^{i a_n}\right).$$
--
--   **Rephasing equivalence.** Two complex $n\times n$ matrices $U$ and $V$ are *rephasing equivalent* when
--   $$V = D(a)\,U\,D(b)\qquad\text{for some real }a,b\in\mathbb R^{n}.$$
--   This is exactly the statement that $V$ is obtained from $U$ by choosing a different phase convention for the $n$ left-handed and $n$ right-handed fields, the operation Kobayashi and Maskawa call "an appropriate phase convention of the quartet field".
--
--   **Real matrices.** A complex matrix is *real* when every entry has vanishing imaginary part.
--
--   **The Cabibbo form, Eq. (6).**
--   $$U(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}.$$
--
--   **The Kobayashi--Maskawa form, Eq. (13).** With $c_i=\cos\theta_i$, $s_i=\sin\theta_i$,
--   $$
--   K(\theta_1,\theta_2,\theta_3,\delta)=
--   \begin{pmatrix}
--   c_1 & -s_1c_3 & -s_1s_3\\
--   s_1c_2 & c_1c_2c_3-s_2s_3e^{i\delta} & c_1c_2s_3+s_2c_3e^{i\delta}\\
--   s_1s_2 & c_1s_2c_3+c_2s_3e^{i\delta} & c_1s_2s_3-c_2c_3e^{i\delta}
--   \end{pmatrix}.
--   $$
--
--   These four notions are what the mission's statements are phrased in: they let "the phases can (cannot) be absorbed into the phase convention of the fields" be stated as a precise algebraic assertion about matrices.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℂ`; the angles and the phase are arbitrary real numbers, with no range restriction, and no positivity or genericity condition is imposed anywhere.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 654 Eq. (5)-(6) and pp. 657 Eq. (13)

import Mathlib

namespace KobayashiMaskawa1973

open Matrix

/-- The diagonal phase matrix `diag(e^{i a₁}, …, e^{i aₙ})`. -/
noncomputable def phaseDiag {n : Type*} [Fintype n] [DecidableEq n] (a : n → ℝ) :
    Matrix n n ℂ :=
  Matrix.diagonal fun k => Complex.exp ((a k : ℂ) * Complex.I)

/-- `V` arises from `U` by a change of the phase convention of the fields:
`V = diag(e^{i a}) * U * diag(e^{i b})` for some real phases `a`, `b`. -/
def RephasingEquiv {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) : Prop :=
  ∃ a b : n → ℝ, phaseDiag a * U * phaseDiag b = V

/-- A complex matrix all of whose entries have vanishing imaginary part. -/
def IsRealMatrix {n : Type*} (M : Matrix n n ℂ) : Prop :=
  ∀ i j, (M i j).im = 0

/-- The real rotation matrix of Eq. (6):
`[[cos θ, sin θ], [-sin θ, cos θ]]`. -/
noncomputable def cabibboMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ);
     -(Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- The 3 × 3 mixing matrix of Eq. (13), with `cᵢ = cos θᵢ`, `sᵢ = sin θᵢ`,
`e = exp (i δ)`. -/
noncomputable def kmMatrix (θ₁ θ₂ θ₃ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let c₁ : ℂ := Real.cos θ₁
  let s₁ : ℂ := Real.sin θ₁
  let c₂ : ℂ := Real.cos θ₂
  let s₂ : ℂ := Real.sin θ₂
  let c₃ : ℂ := Real.cos θ₃
  let s₃ : ℂ := Real.sin θ₃
  let e : ℂ := Complex.exp ((δ : ℂ) * Complex.I)
  !![c₁,      -s₁ * c₃,                    -s₁ * s₃;
     s₁ * c₂, c₁ * c₂ * c₃ - s₂ * s₃ * e,  c₁ * c₂ * s₃ + s₂ * c₃ * e;
     s₁ * s₂, c₁ * s₂ * c₃ + c₂ * s₃ * e,  c₁ * s₂ * s₃ - c₂ * c₃ * e]

end KobayashiMaskawa1973


