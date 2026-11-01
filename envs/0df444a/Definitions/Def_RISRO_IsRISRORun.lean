-- Prove2me | Definitions.Def_RISRO_IsRISRORun
-- name    : RISRO_IsRISRORun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:32:46.503983+00:00
-- url     : https://prove2.me/theorems/0a260c6a-e9f5-40a3-a483-df3398a453da
-- title:
--   A run of RISRO (Algorithm 1)
-- statement:
--   Sequences $X^t,U^t,U^t_\perp,V^t,V^t_\perp,B^t,D_1^t,D_2^t$ form a **run of RISRO** for $(\mathcal A,y,r)$ when:
--
--   1. for every $t$, $U^t\in\mathbb O_{p_1,r}$, $V^t\in\mathbb O_{p_2,r}$ with orthonormal complements $U^t_\perp$, $V^t_\perp$;
--   2. the input factors as $X^0=U^0S\,V^{0\top}$ with $S\in\mathbb R^{r\times r}$;
--   3. $(B^{t+1},D_1^{t+1},D_2^{t+1})$ solves the least squares problem (5) built from $U^t,U^t_\perp,V^t,V^t_\perp$;
--   4. with $X_U^{t+1}=U^tB^{t+1}+U^t_\perp D_1^{t+1}$ and $X_V^{t+1}=V^tB^{t+1\top}+V^t_\perp D_2^{t+1}$, one has $X_U^{t+1}=U^{t+1}R$ and $X_V^{t+1}=V^{t+1}R'$ for some $r\times r$ matrices $R,R'$;
--   5. $X^{t+1}=X_U^{t+1}(B^{t+1})^\dagger X_V^{t+1\top}$.
--
--   **Formalization Note.** This is a relation: the factorization of $X^0$, the complements, the minimizer and the orthogonalization stay free, because Algorithm 1 does not fix them. Every QR factorization of $X_U^{t+1}$ and $X_V^{t+1}$ satisfies clause 4. An SVD of $X^0$ is a special case of clause 2. The Moore–Penrose inverse is specified by the four Penrose equations.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Algorithm 1, p.6

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_InputSparsity_Regress_Basic
import Definitions.Def_RISRO_IsFrame
import Definitions.Def_RISRO_IsLSMinimizer

open HighDimStat.MatrixRank Matrix InputSparsity.Regress

namespace RISRO

/-- `(X^t, U^t, U_⊥^t, V^t, V_⊥^t, B^t, D₁^t, D₂^t)` is a run of RISRO (Algorithm 1):

1. at every `t`, `U^t`, `V^t` are orthonormal with orthonormal complements `U_⊥^t`, `V_⊥^t`;
2. the input `X⁰` factors as `U⁰ S V⁰ᵀ` with an `r × r` matrix `S` (step 1);
3. `(B^{t+1}, D₁^{t+1}, D₂^{t+1})` solves the least squares problem (5) at `t` (steps 3–4);
4. `X_U^{t+1} = U^t B^{t+1} + U_⊥^t D₁^{t+1}` and `X_V^{t+1} = V^t (B^{t+1})ᵀ + V_⊥^t D₂^{t+1}`
   (step 5) lie in the spans of `U^{t+1}` and `V^{t+1}` (step 6);
5. `X^{t+1} = X_U^{t+1} (B^{t+1})† (X_V^{t+1})ᵀ` (step 7).

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Algorithm 1, p.6.

Formalization Notes: every choice the algorithm leaves open stays open (the factorization of `X⁰`,
the complements, the minimizer of (5), the orthogonalization): this is a relation, not a function.
Step 6 is relaxed to `X_U = U^{t+1} R` for some `r × r` matrix `R`, which every QR factorization
satisfies. `S` is any `r × r` matrix; an SVD is a special case. `B`, `D₁`, `D₂` are indexed as on
the page, so `B 0`, `D₁ 0`, `D₂ 0` are unconstrained and unused. `(B^{t+1})†` is any `G` with
`IsMoorePenrose (B (t + 1)) G`; the four Penrose equations determine it uniquely. -/
structure IsRISRORun {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (X : ℕ → Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : ℕ → Matrix (Fin p₁) (Fin r) ℝ) (Uc : ℕ → Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : ℕ → Matrix (Fin p₂) (Fin r) ℝ) (Vc : ℕ → Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : ℕ → Matrix (Fin r) (Fin r) ℝ) (D₁ : ℕ → Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : ℕ → Matrix (Fin (p₂ - r)) (Fin r) ℝ) : Prop where
  frameU : ∀ t, IsFrame (U t) (Uc t)
  frameV : ∀ t, IsFrame (V t) (Vc t)
  init : ∃ S : Matrix (Fin r) (Fin r) ℝ, X 0 = U 0 * S * (V 0)ᵀ
  leastSquares : ∀ t, IsLSMinimizer A y (U t) (Uc t) (V t) (Vc t) (B (t + 1)) (D₁ (t + 1)) (D₂ (t + 1))
  spanU : ∀ t, ∃ R : Matrix (Fin r) (Fin r) ℝ, U t * B (t + 1) + Uc t * D₁ (t + 1) = U (t + 1) * R
  spanV : ∀ t, ∃ R : Matrix (Fin r) (Fin r) ℝ, V t * (B (t + 1))ᵀ + Vc t * D₂ (t + 1) = V (t + 1) * R
  update : ∀ t, ∃ G : Matrix (Fin r) (Fin r) ℝ, IsMoorePenrose (B (t + 1)) G ∧
    X (t + 1) = (U t * B (t + 1) + Uc t * D₁ (t + 1)) * G *
      (V t * (B (t + 1))ᵀ + Vc t * D₂ (t + 1))ᵀ

end RISRO


