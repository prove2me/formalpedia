-- Prove2me | Definitions.Def_FixedPointAA_Main_Setting
-- name    : FixedPointAA_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:27.636289+00:00
-- url     : https://prove2.me/theorems/7f81d18e-0873-4ec2-a962-c155febeac1e
-- title:
--   pp. 1–3, Eqs. (1), (4), (6)–(11), (13)–(15) — search operators and Chebyshev data
-- statement:
--   Let $s$ and $T$ be unit states in a finite-dimensional complex space, and let $S_s(\alpha)$ and $S_T(\beta)$ be their phase reflections. The generalized iterate and its ordered product are
--
--   $$G(\alpha,\beta)=-S_s(\alpha)S_T(\beta),\qquad \mathcal S_{2l+1}=G(\alpha_l,\beta_l)\cdots G(\alpha_1,\beta_1).$$
--
--   This module also defines the Chebyshev polynomial $T_L$, the real branch $\gamma^{-1}=T_{1/L}(1/\delta)$, the phases of Eq. (11), the success-probability function $P_L(\lambda,\delta)$, the width $w$, and the two-dimensional states and rotations used on pp. 2–3. These shared definitions fix the conventions for every theorem in the mission.
--
--   **Formalization Note** The rank-one operator uses $|T\rangle\langle T|=|t\rangle\langle t|$ because $t$ differs from $T$ by a unit complex phase. The definitions are total, but theorems impose $0<\delta\le1$ and the appropriate overlap conditions.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, pp. 1–3, Eqs. (1), (4), (6)–(11), (13)–(15)

import Mathlib

namespace FixedPointAA.Main

open scoped Matrix

/-- Eq. (6), acting on the full finite-dimensional state space. -/
noncomputable def Ss {N : ℕ} (s : Fin N → ℂ) (α : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) • Matrix.vecMulVec s (star s)

/-- Eq. (7); the projector is unchanged when `T` is replaced by `t = exp (-iξ) T`. -/
noncomputable def St {N : ℕ} (T : Fin N → ℂ) (β : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - (1 - Complex.exp ((β : ℂ) * Complex.I)) • Matrix.vecMulVec T (star T)

/-- The generalized Grover iterate following Eq. (7). -/
noncomputable def G {N : ℕ} (s T : Fin N → ℂ) (α β : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  -(Ss s α * St T β)

/-- Eq. (10), with the iterate numbered `1` acting first. -/
noncomputable def seqOp {N : ℕ} (s T : Fin N → ℂ) (α β : ℕ → ℝ) :
    ℕ → Matrix (Fin N) (Fin N) ℂ
  | 0 => 1
  | j + 1 => G s T (α (j + 1)) (β (j + 1)) * seqOp s T α β j

/-- The actual Chebyshev polynomial, including outside `[-1,1]`. -/
noncomputable def chebT (L : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval x

/-- The positive real branch of `T_{1/L}(1/δ)` for `δ ∈ (0,1]`. -/
noncomputable def gammaInv (L : ℕ) (δ : ℝ) : ℝ :=
  Real.cosh (Real.arcosh (1 / δ) / (L : ℝ))

noncomputable def gam (L : ℕ) (δ : ℝ) : ℝ := 1 / gammaInv L δ

/-- The inverse cotangent branch with values in `(0,π)`. -/
noncomputable def arccot (y : ℝ) : ℝ := Real.pi / 2 - Real.arctan y

/-- Eq. (11), used for `1 ≤ j ≤ l`. -/
noncomputable def alpha (l : ℕ) (δ : ℝ) (j : ℕ) : ℝ :=
  2 * arccot (Real.tan (2 * Real.pi * (j : ℝ) / (2 * (l : ℝ) + 1)) *
    Real.sqrt (1 - gam (2 * l + 1) δ ^ 2))

/-- Eq. (11), used for `1 ≤ j ≤ l`. -/
noncomputable def beta (l : ℕ) (δ : ℝ) (j : ℕ) : ℝ :=
  -alpha l δ (l + 1 - j)

/-- Eq. (1) as a function of the overlap probability and error parameter. -/
noncomputable def PL (L : ℕ) (lam δ : ℝ) : ℝ :=
  1 - δ ^ 2 * chebT L (gammaInv L δ * Real.sqrt (1 - lam)) ^ 2

/-- The width following Eq. (1), p. 2. -/
noncomputable def width (L : ℕ) (δ : ℝ) : ℝ :=
  1 - 1 / gammaInv L δ ^ 2

/-- Pauli X. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli Y. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli Z. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Bloch-sphere rotation `R_ϕ(θ)` on p. 2. -/
noncomputable def R (ϕ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ)) •
    ((Real.cos ϕ : ℂ) • pauliZ + (Real.sin ϕ : ℂ) • pauliX))

/-- The equatorial rotation `A_ζ` on p. 3. -/
noncomputable def A (φ ζ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (-(Complex.I * ((φ / 2 : ℝ) : ℂ)) •
    ((Real.cos ζ : ℂ) • pauliX + (Real.sin ζ : ℂ) • pauliY))

/-- Eq. (4) in the basis `|t̄⟩, |t⟩`. -/
noncomputable def sVec (lam : ℝ) : Fin 2 → ℂ :=
  ![(Real.sqrt (1 - lam) : ℂ), (Real.sqrt lam : ℂ)]

def tVec : Fin 2 → ℂ := ![0, 1]
def tbarVec : Fin 2 → ℂ := ![1, 0]

noncomputable def blochAngle (lam : ℝ) : ℝ :=
  2 * Real.arcsin (Real.sqrt lam)

/-- The phase difference in Eq. (13). -/
noncomputable def dz (l : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.pi -
    2 * arccot (Real.tan ((k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)) *
      Real.sqrt (1 - gam (2 * l + 1) δ ^ 2))

/-- The solution of Eq. (13) anchored at `ζ_{l+1} = (-1)^l π/2`. -/
noncomputable def zeta (l : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ l * Real.pi / 2 +
    (∑ i ∈ Finset.Ico 1 k, dz l δ i) -
    (∑ i ∈ Finset.Ico 1 (l + 1), dz l δ i)

/-- Ordered product `A_{ζ_h} ⋯ A_{ζ_1}`. -/
noncomputable def Aprod (φ : ℝ) (ζ : ℕ → ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | h + 1 => A φ (ζ (h + 1)) * Aprod φ ζ h

/-- Upper component `a_h` of Eq. (14). -/
noncomputable def amp (φ : ℝ) (ζ : ℕ → ℝ) (h : ℕ) : ℂ :=
  (Aprod φ ζ h *ᵥ tbarVec) 0

end FixedPointAA.Main


