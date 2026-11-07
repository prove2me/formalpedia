-- Prove2me | Definitions.Def_FermiGaussMix_IsPropagator
-- name    : FermiGaussMix_IsPropagator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:59:54.795292+00:00
-- url     : https://prove2.me/theorems/a2d4f320-d186-4f38-84c1-3dabcb2e18b3
-- title:
--   The interaction picture: $G$, $X(u)$, $A(u)$, $A^S$, the propagator equation and $\eta_q$
-- statement:
--   With $T=\beta/2$ and $H=H_0+V$, set
--   $$
--   G=e^{-TH_0},\qquad X(u)=e^{uH_0}e^{-uH},\qquad A(u)=e^{uH_0}Ve^{-uH_0}.
--   $$
--   For $S\subseteq[2n]$ and $Y=\sum_Ry_RP_R$, the operator $Y^S=\sum_{R\subseteq S}y_RP_R$ keeps the monomials supported in $S$. A propagator for a family $A(\cdot)$ on $[0,T]$ is a solution of
--   $$
--   \frac{d}{du}X(u)=-A(u)X(u),\qquad X(0)=\mathbf 1 ,
--   $$
--   which is the time-ordered exponential $\mathcal T\exp(-\int_0^uA(v)\,dv)$. Finally $\eta_q=\int_0^TJ_q(A(u))\,du$.
--
--   **Formalization Note** Mathlib has no time-ordered exponential, so $X^S$ is characterized by its equation, which has a unique solution. The derivative is taken entrywise and within $[0,T]$.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (B.1), p. 11; (B.64)–(B.65), p. 18; (B.79)–(B.80), (B.85), p. 20

import Mathlib
import Definitions.Def_FermiGaussMix_coeff

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- `G = e^{-T H₀}`, eq. (B.1), p.11 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def gOp {n : ℕ} (T : ℝ) (H0 : Op n) : Op n :=
  NormedSpace.exp ((-T : ℂ) • H0)

/-- `X(u) = e^{u H₀} e^{-u H}` with `H = H₀ + V`, eqs. (B.1), p.11, and (B.64), p.18 (Han, Zhao, Liu,
arXiv:2609.35159v1). The operator `X` of (B.1) is `xOp T H0 V`, with `T = β/2`. -/
noncomputable def xOp {n : ℕ} (u : ℝ) (H0 V : Op n) : Op n :=
  NormedSpace.exp ((u : ℂ) • H0) * NormedSpace.exp ((-u : ℂ) • (H0 + V))

/-- `A(u) = e^{u H₀} V e^{-u H₀}`, eq. (B.64), p.18 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def interaction {n : ℕ} (H0 V : Op n) (u : ℝ) : Op n :=
  NormedSpace.exp ((u : ℂ) • H0) * V * NormedSpace.exp ((-u : ℂ) • H0)

/-- `A^S`: the part of `Y = Σ_R y_R P_R` made of the monomials supported in `S`, eq. (B.79), p.20 (Han, Zhao,
Liu, arXiv:2609.35159v1). -/
noncomputable def restrict {n : ℕ} (S : Finset (Fin (2 * n))) (Y : Op n) : Op n :=
  ∑ R ∈ (evenSets n).filter (fun R => R ⊆ S), coeff Y R • P n R

/-- `X` solves `X' = -A X`, `X(0) = 1` on `[0, T]`: eq. (B.65), p.18, and the derivative form of
`X^S(u) = T exp(-∫_0^u A^S(v) dv)`, eq. (B.80), p.20 (Han, Zhao, Liu, arXiv:2609.35159v1).

**Formalization Note** Mathlib has no time-ordered exponential, so `X^S` is any solution of its equation. With
`T > 0` and continuous `A` a solution exists and is unique. The derivative is taken entrywise and within
`[0, T]`, so no norm on matrices is involved. -/
def IsPropagator {n : ℕ} (T : ℝ) (A X : ℝ → Op n) : Prop :=
  X 0 = 1 ∧ ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ x y,
    HasDerivWithinAt (fun v => X v x y) (-((A u * X u) x y)) (Set.Icc (0 : ℝ) T) u

/-- `η_q = ∫_0^T J_q(A(u)) du`, eq. (B.85), p.20 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def etaQ {n : ℕ} (q T : ℝ) (A : ℝ → Op n) : ℝ :=
  ∫ u in (0 : ℝ)..T, Jq q (A u)

end FermiGaussMix


