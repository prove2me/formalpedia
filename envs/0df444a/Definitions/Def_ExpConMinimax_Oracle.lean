-- Prove2me | Definitions.Def_ExpConMinimax_Oracle
-- name    : ExpConMinimax_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:31.148842+00:00
-- url     : https://prove2.me/theorems/22b15593-62c7-4978-8383-925061c9675c
-- title:
--   The sampling oracle (SO) and the per-iteration sample tuple
-- statement:
--   The **sampling oracle** consists of probability laws $P_\omega,P_\xi,P_\zeta$ of random vectors $\omega,\xi,\zeta$ and maps returning
--
--   1. sampled subgradients $\widetilde\nabla_xf(x,y,\omega)\in\mathbb R^{d_x}$ and $\widetilde\nabla_yf(x,y,\omega)\in\mathbb R^{d_y}$;
--   2. a sampled value $h(x,\xi)\in\mathbb R^{m_1}$ and a sampled Jacobian $\widetilde\nabla_xh(x,\xi)\in\mathbb R^{d_x\times m_1}$ whose $i$-th column is $\widetilde\nabla h_i(x,\xi)$;
--   3. a sampled value $g(y,\zeta)\in\mathbb R^{m_2}$ and a sampled Jacobian $\widetilde\nabla_yg(y,\zeta)\in\mathbb R^{d_y\times m_2}$.
--
--   The definition also records their means $\widetilde\nabla_xF(x,y)=\mathbb E[\widetilde\nabla_xf(x,y,\omega)]$, $\widetilde\nabla_yF$, $\widetilde\nabla H(x)=\mathbb E[\widetilde\nabla h(x,\xi)]$ and $\widetilde\nabla G(y)$, the joint measurability of the maps, and the **sample tuple** $(\omega^1_t,\omega^2_t,\xi^1_t,\xi^2_t,\zeta^1_t,\zeta^2_t)$ drawn in iteration $t$ of Algorithm 1 (two independent queries).
--
--   **Formalization Note** A $d_x\times m_1$ matrix is a linear map $\mathbb R^{m_1}\to\mathbb R^{d_x}$, so $\sum_i\gamma_i\widetilde\nabla h_i(x,\xi)$ is that map applied to $\gamma$, and its norm is the operator norm.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, §2, pp.8–9 (sampling oracle (i)–(iii)); §3, p.10 (two queries per iteration)

import Mathlib
import Definitions.Def_ExpConMinimax_Vec

namespace ExpConMinimax

open MeasureTheory

/-- **The sampling oracle (SO).**
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, §2, pp.8–9:

(i) given `x ∈ X`, `y ∈ Y`, the SO returns sampled sub-gradients `∇̃ₓf(x,y,ω) ∈ ℝ^{d_x}` and
`∇̃_yf(x,y,ω) ∈ ℝ^{d_y}`;
(ii) given `x ∈ X`, it returns a sampled noisy vector `h(x,ξ) ∈ ℝ^{m₁}` and a sampled gradient
`∇̃ₓh(x,ξ) ∈ ℝ^{d_x×m₁}`;
(iii) given `y ∈ Y`, it returns a sampled noisy vector `g(y,ζ) ∈ ℝ^{m₂}` and a sampled
sub-gradient `∇̃_yg(y,ζ) ∈ ℝ^{d_y×m₂}`.

The random vectors `ω`, `ξ`, `ζ` take values in the sample spaces `Sω`, `Sξ`, `Sζ` and have the
laws `μω`, `μξ`, `μζ`.

**Formalization Note.** The `d_x × m₁` matrix `∇̃ₓh(x,ξ)`, whose `i`-th column is `∇̃hᵢ(x,ξ)`,
is the linear map `ghs x ξ : ℝ^{m₁} → ℝ^{d_x}`, so that `∑ᵢ γᵢ ∇̃hᵢ(x,ξ) = ghs x ξ γ`; its norm
is the operator norm. The same holds for `ggs`. -/
structure Oracle (dx dy m₁ m₂ : ℕ) (Sω Sξ Sζ : Type*) [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] where
  /-- Sampled sub-gradient `∇̃ₓf(x,y,ω)`. -/
  gfx : Vec dx → Vec dy → Sω → Vec dx
  /-- Sampled (super-)gradient `∇̃_yf(x,y,ω)`. -/
  gfy : Vec dx → Vec dy → Sω → Vec dy
  /-- Sampled constraint value `h(x,ξ)`. -/
  hs : Vec dx → Sξ → Vec m₁
  /-- Sampled constraint Jacobian `∇̃ₓh(x,ξ)` (columns `∇̃hᵢ(x,ξ)`). -/
  ghs : Vec dx → Sξ → (Vec m₁ →L[ℝ] Vec dx)
  /-- Sampled constraint value `g(y,ζ)`. -/
  gs : Vec dy → Sζ → Vec m₂
  /-- Sampled constraint Jacobian `∇̃_yg(y,ζ)` (columns `∇̃gⱼ(y,ζ)`). -/
  ggs : Vec dy → Sζ → (Vec m₂ →L[ℝ] Vec dy)
  /-- Law of `ω`. -/
  μω : Measure Sω
  /-- Law of `ξ`. -/
  μξ : Measure Sξ
  /-- Law of `ζ`. -/
  μζ : Measure Sζ

namespace Oracle

variable {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω] [MeasurableSpace Sξ]
  [MeasurableSpace Sζ]

/-- `∇̃ₓF(x,y) := E[∇̃ₓf(x,y,ω)]` (Assumption 2.1, p.9). -/
noncomputable def meanGfx (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy) :
    Vec dx :=
  ∫ s, O.gfx x y s ∂O.μω

/-- `∇̃_yF(x,y) := E[∇̃_yf(x,y,ω)]` (Assumption 2.1, p.9). -/
noncomputable def meanGfy (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) (y : Vec dy) :
    Vec dy :=
  ∫ s, O.gfy x y s ∂O.μω

/-- `∇̃H(x) := E[∇̃h(x,ξ)]` (Assumption 2.2, p.9), a linear map whose `i`-th column is
`∇̃Hᵢ(x)`. -/
noncomputable def meanGhs (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (x : Vec dx) :
    Vec m₁ →L[ℝ] Vec dx :=
  ∫ s, O.ghs x s ∂O.μξ

/-- `∇̃G(y) := E[∇̃g(y,ζ)]` (Assumption 2.2, p.9), a linear map whose `j`-th column is
`∇̃Gⱼ(y)`. -/
noncomputable def meanGgs (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (y : Vec dy) :
    Vec m₂ →L[ℝ] Vec dy :=
  ∫ s, O.ggs y s ∂O.μζ

/-- **Measurability of the oracle maps.** Each oracle output is jointly (strongly) measurable in
the query point and the sample, so that the outputs at random query points are random
variables (§2, p.8: the SO returns random vectors). -/
def IsMeasurable (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) : Prop :=
  StronglyMeasurable (fun p : Vec dx × Vec dy × Sω => O.gfx p.1 p.2.1 p.2.2) ∧
  StronglyMeasurable (fun p : Vec dx × Vec dy × Sω => O.gfy p.1 p.2.1 p.2.2) ∧
  StronglyMeasurable (fun p : Vec dx × Sξ => O.hs p.1 p.2) ∧
  StronglyMeasurable (fun p : Vec dx × Sξ => O.ghs p.1 p.2) ∧
  StronglyMeasurable (fun p : Vec dy × Sζ => O.gs p.1 p.2) ∧
  StronglyMeasurable (fun p : Vec dy × Sζ => O.ggs p.1 p.2)

end Oracle

/-- **The per-iteration sample tuple** `(ω¹ₜ, ω²ₜ, ξ¹ₜ, ξ²ₜ, ζ¹ₜ, ζ²ₜ)`.
arXiv:2202.07868v2, §3, p.10: "In iteration `t`, we query the SO at `(xₜ,yₜ)` twice …
`{ωʲₜ, ξʲₜ, ζʲₜ}_{j=1,2}` represents two independent realizations of random variables `ω, ξ, ζ`
in iteration `t`."

**Formalization Note.** The tuple is the nested product `Sω × Sω × Sξ × Sξ × Sζ × Sζ`; the
accessors `ω1`, `ω2`, `ξ1`, `ξ2`, `ζ1`, `ζ2` below name its components. -/
abbrev SampleTuple (Sω Sξ Sζ : Type*) : Type _ := Sω × Sω × Sξ × Sξ × Sζ × Sζ

namespace SampleTuple

variable {Sω Sξ Sζ : Type*}

/-- `ω¹ₜ`. -/
def ω1 (s : SampleTuple Sω Sξ Sζ) : Sω := s.1
/-- `ω²ₜ`. -/
def ω2 (s : SampleTuple Sω Sξ Sζ) : Sω := s.2.1
/-- `ξ¹ₜ`. -/
def ξ1 (s : SampleTuple Sω Sξ Sζ) : Sξ := s.2.2.1
/-- `ξ²ₜ`. -/
def ξ2 (s : SampleTuple Sω Sξ Sζ) : Sξ := s.2.2.2.1
/-- `ζ¹ₜ`. -/
def ζ1 (s : SampleTuple Sω Sξ Sζ) : Sζ := s.2.2.2.2.1
/-- `ζ²ₜ`. -/
def ζ2 (s : SampleTuple Sω Sξ Sζ) : Sζ := s.2.2.2.2.2

end SampleTuple

end ExpConMinimax


