-- Prove2me | Definitions.Def_TechBreakthrough_Model_stopRegion
-- name    : TechBreakthrough_Model_stopRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:22.56198+00:00
-- url     : https://prove2.me/theorems/480801dc-9b3d-4722-86a6-0b2a58fec761
-- title:
--   The regions $J$, $S$, $C$, $J_{\underline m}$, $J_1$, $J_2$, $J_3$
-- statement:
--   The state space of $(X,M)$ is $J=\{(x,m)\in\mathcal I\times\mathcal I:m\ge x\}$. Given $x_R$, $\underline m$ and $b$:
--
--   $$S=\{(x,m)\in J:\underline m\le m<\beta,\ x_R\le x\le b(m)\},\qquad C=J\setminus S,$$
--
--   $$J_{\underline m}=\{(x,\underline m)\in J:x\in(\alpha,\underline m]\},\quad J_1=\{(x,m)\in J:m\in[\underline m,\beta),\ x\le x_R\},$$
--
--   $$J_2=\{(x,m)\in J:m\in[\underline m,\beta),\ x\ge b(m)\},\quad J_3=\{(x,m)\in J:m\in(\alpha,\underline m]\}.$$
--
--   $S$ is the stopping region and $C$ the continuation region. $J_{\underline m}$ is a horizontal segment, the only place where a function of the class $\mathcal V$ may fail to be $C^1$.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, §5, p.15; p.18

import Definitions.Def_TechBreakthrough_Model

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The state space `J = {(x, m) ∈ 𝓘 × 𝓘 : m ≥ x}`, arXiv:2106.05112v1, §5, p.15. -/
def domain : Set (ℝ × ℝ) := {z | z.1 ∈ M.I ∧ z.2 ∈ M.I ∧ z.1 ≤ z.2}

/-- The interval `[a, β)`. -/
def fromLevel (a : ℝ) : Set ℝ := {m | a ≤ m ∧ m ∈ M.I}

/-- The stopping region `S = {(x, m) ∈ J : m̲ ≤ m < β and x_R ≤ x ≤ b(m)}`, arXiv:2106.05112v1,
p.18. -/
def stopRegion (xR mLow : ℝ) (b : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z ∈ M.domain | mLow ≤ z.2 ∧ xR ≤ z.1 ∧ z.1 ≤ b z.2}

/-- The continuation region `C = J \ S`, arXiv:2106.05112v1, p.18. -/
def contRegion (xR mLow : ℝ) (b : ℝ → ℝ) : Set (ℝ × ℝ) :=
  M.domain \ M.stopRegion xR mLow b

/-- `J_m̲ = {(x, m̲) ∈ J : x ∈ (α, m̲]}`, a horizontal segment, arXiv:2106.05112v1, p.18. -/
def segmentLow (mLow : ℝ) : Set (ℝ × ℝ) := {z ∈ M.domain | z.2 = mLow}

/-- `J₁ = {(x, m) ∈ J : m ∈ [m̲, β) and x ≤ x_R}`, arXiv:2106.05112v1, p.18. -/
def wedge₁ (xR mLow : ℝ) : Set (ℝ × ℝ) := {z ∈ M.domain | mLow ≤ z.2 ∧ z.1 ≤ xR}

/-- `J₂ = {(x, m) ∈ J : m ∈ [m̲, β) and x ≥ b(m)}`, arXiv:2106.05112v1, p.18. -/
def wedge₂ (mLow : ℝ) (b : ℝ → ℝ) : Set (ℝ × ℝ) := {z ∈ M.domain | mLow ≤ z.2 ∧ b z.2 ≤ z.1}

/-- `J₃ = {(x, m) ∈ J : m ∈ (α, m̲]}`, arXiv:2106.05112v1, p.18. -/
def wedge₃ (mLow : ℝ) : Set (ℝ × ℝ) := {z ∈ M.domain | z.2 ≤ mLow}

end Model

end TechBreakthrough


