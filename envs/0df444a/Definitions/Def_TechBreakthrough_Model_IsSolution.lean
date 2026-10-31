-- Prove2me | Definitions.Def_TechBreakthrough_Model_IsSolution
-- name    : TechBreakthrough_Model_IsSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:08.212964+00:00
-- url     : https://prove2.me/theorems/3a64ba99-4b0c-470b-ab84-fe2c63b166df
-- title:
--   The class $\mathcal V$ and the variational system (VS)
-- statement:
--   The class is
--
--   $$\mathcal V\equiv C^0(J)\cap C^1(J\setminus J_{\underline m})\cap C^{2,1}(J_1)\cap C^{2,1}(J_2)\cap C^{2,1}(J_3)\cap C^{2,1}(S).$$
--
--   $(\underline m,b,W)$ is a solution in $(x_R,\beta)\times C^1([\underline m,\beta))\times\mathcal V$ when
--
--   $$b(\underline m)=x_R,\quad x_R\le b(m)<m\ \ (m\in[\underline m,\beta)),\quad\lim_{m\to\beta^-}b(m)=\beta,$$
--
--   $$\mathcal LW(x,m)-rW(x,m)=0\ \ \text{on int }C,\qquad W(x,m)=[1-F(m)]R(x)\ \ \text{on }S,$$
--
--   $$\frac{\partial W}{\partial x}(b(m),m)=[1-F(m)]R'(b(m))\ \ (m\in[\underline m,\beta)),\quad\frac{\partial W}{\partial m}(m,m)=-f(m)G(m),\quad\lim_{x\to\alpha^+}W(x,m)=0\ \ (m\in\mathcal I).$$
--
--   These are (25)–(32): dynamic programming, value matching, smooth fit, the Neumann condition at the diagonal and the boundary condition at $\alpha$.
--
--   **Formalization Note** $b$ and $W$ are total functions, read only on $[\underline m,\beta)$ and $J$. (30) is two-sided; (31) is a right derivative, $W(m,m')$ being undefined for $m'<m$. Strict monotonicity of $b$ is not part of this definition: it is a conclusion of Theorem 1.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (25)–(32), pp.17–18; class 𝒱, p.18

import Definitions.Def_TechBreakthrough_Model_stopRegion
import Definitions.Def_TechBreakthrough_IsC21On

open Filter
open scoped Topology

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- `W ∈ 𝒱 ≡ C⁰(J) ∩ C¹(J \ J_m̲) ∩ C^{2,1}(J₁) ∩ C^{2,1}(J₂) ∩ C^{2,1}(J₃) ∩ C^{2,1}(S)`,
arXiv:2106.05112v1, Theorem 1, p.18. -/
structure InClassV (xR mLow : ℝ) (b : ℝ → ℝ) (W : ℝ → ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn (Function.uncurry W) M.domain
  c1 : IsC1On W (M.domain \ M.segmentLow mLow)
  c21₁ : IsC21On W (M.wedge₁ xR mLow)
  c21₂ : IsC21On W (M.wedge₂ mLow b)
  c21₃ : IsC21On W (M.wedge₃ mLow)
  c21S : IsC21On W (M.stopRegion xR mLow b)

/-- `(m̲, b, W)` is a solution of the variational system (VS) (25)–(32) in the class
`(x_R, β) × C¹([m̲, β)) × 𝒱` of Theorem 1, arXiv:2106.05112v1, pp.17–18.

**Formalization Note** `b` and `W` are total functions, used only on `[m̲, β)` and `J`. (27) and
(32) are limits along `atRightEnd` and `atLeftEnd`, with (27) valued in `EReal`. (30) is a
two-sided derivative of `W(·, m)`. (31) is the right derivative of `W(m, ·)` at `m`, since `W` is
undefined for second argument below `m`. Strict monotonicity of `b` is **not** part of this
definition. -/
structure IsSolution (xR mLow : ℝ) (b : ℝ → ℝ) (W : ℝ → ℝ → ℝ) : Prop where
  xR_lt : xR < mLow
  mLow_mem : mLow ∈ M.I
  b_contDiffOn : ContDiffOn ℝ 1 b (M.fromLevel mLow)
  classV : M.InClassV xR mLow b W
  eq25 : b mLow = xR
  eq26 : ∀ m ∈ M.fromLevel mLow, xR ≤ b m ∧ b m < m
  eq27 : Tendsto (fun m => (b m : EReal)) M.atRightEnd (𝓝 M.β)
  eq28 : ∀ z ∈ interior (M.contRegion xR mLow b),
    M.gen (fun y => W y z.2) z.1 - M.r * W z.1 z.2 = 0
  eq29 : ∀ z ∈ M.stopRegion xR mLow b, W z.1 z.2 = (1 - M.F z.2) * M.R z.1
  eq30 : ∀ m ∈ M.fromLevel mLow,
    HasDerivAt (fun y => W y m) ((1 - M.F m) * deriv M.R (b m)) (b m)
  eq31 : ∀ m ∈ M.I, HasDerivWithinAt (fun n => W m n) (-M.f m * M.G m) (Set.Ici m) m
  eq32 : ∀ m ∈ M.I, Tendsto (fun x => W x m) M.atLeftEnd (𝓝 0)

end Model

end TechBreakthrough


