-- Prove2me | Definitions.Def_CandesTao_Decoding_L1Minimization
-- name    : CandesTao_Decoding_L1Minimization
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-30T22:04:00.260377+00:00
-- url     : https://prove2.me/theorems/a73c1962-ce02-428a-a745-1b4b92e412d0
-- title:
--   Unique minimizer of the $\ell^1$ programs $(P_1)$ and $(P_1')$
-- statement:
--   Two predicates record what it means for a vector to be *the* unique solution of the paper's two $\ell^1$-minimization problems.
--
--   1. For a real $p \times m$ matrix $F$, data $f \in \mathbb{R}^p$ and a vector $c \in \mathbb{R}^m$: $c$ is the **unique minimizer** of
--   $$
--   (P_1)\qquad \min_{d \in \mathbb{R}^m} \|d\|_{\ell^1} \quad \text{subject to} \quad Fd = f
--   $$
--   when $Fc = f$ and every other feasible vector $d$ (that is, $Fd = f$ and $d \ne c$) satisfies $\|c\|_{\ell^1} < \|d\|_{\ell^1}$ (equation (1.4)).
--
--   2. For a real $m \times n$ matrix $A$, data $y \in \mathbb{R}^m$ and a vector $f \in \mathbb{R}^n$: $f$ is the **unique minimizer** of
--   $$
--   (P_1')\qquad \min_{g \in \mathbb{R}^n} \|y - Ag\|_{\ell^1}
--   $$
--   when every $g \ne f$ satisfies $\|y - Af\|_{\ell^1} < \|y - Ag\|_{\ell^1}$ (equation (1.5)).
--
--   Both problems can be recast as linear programs (equation (1.6)), which is what makes the recovery guarantees of the mission algorithmic; the paper shows (Section 1.3) that $f$ solves $(P_1')$ uniquely if and only if $e$ solves $(P_1)$ uniquely when $y = Af + e$ and $F$ annihilates $A$.
--
--   **Formalization Note** "Unique minimizer" is encoded as a strict inequality against every competitor. This is equivalent to "a minimizer exists and it is the only one", with the minimum attained at the named vector.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 3, eq. (1.4) (P1); p. 4, eq. (1.5) (P1') and eq. (1.6); p. 6, Theorems 1.4 and 1.5 ("unique minimizer")

import Definitions.Def_CandesTao_Decoding_Norms

namespace CandesTao.Decoding

/-- `c` is the unique minimizer of `(P₁)  min ‖d‖_{ℓ¹}  subject to  F d = f`:
`c` is feasible, and every other feasible vector has strictly larger ℓ¹ norm. -/
def IsUniqueL1Minimizer {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (f : Fin p → ℝ)
    (c : Fin m → ℝ) : Prop :=
  F.mulVec c = f ∧ ∀ d : Fin m → ℝ, F.mulVec d = f → d ≠ c → l1Norm c < l1Norm d

/-- `f` is the unique minimizer of `(P₁')  min_{g ∈ ℝⁿ} ‖y - A g‖_{ℓ¹}`:
every `g ≠ f` has a strictly larger residual ℓ¹ norm. -/
def IsUniqueResidualL1Minimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (f : Fin n → ℝ) : Prop :=
  ∀ g : Fin n → ℝ, g ≠ f → l1Norm (y - A.mulVec f) < l1Norm (y - A.mulVec g)

end CandesTao.Decoding


