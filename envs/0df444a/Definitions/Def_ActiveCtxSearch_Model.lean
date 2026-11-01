-- Prove2me | Definitions.Def_ActiveCtxSearch_Model
-- name    : ActiveCtxSearch_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:19.808135+00:00
-- url     : https://prove2.me/theorems/31f1f848-ff38-482d-89ab-e25ad62d4657
-- title:
--   The contextual-search model and Assumptions (A1)–(A3)
-- statement:
--   Contexts live in $\mathbb R^d$ with the Euclidean norm; $B_2(d)=\{x:\|x\|_2\le 1\}$ is the unit ball and $P_U$ the uniform distribution on it, with density $f_u=\mathbf 1_{B_2(d)}/\mathrm{vol}(B_2(d))$.
--
--   An **instance** consists of a coefficient vector $w^*\in\mathbb R^d$, an intercept $\mu^*\in\mathbb R$, a context distribution $P_X$ on $\mathbb R^d$ and a noise distribution $P_\xi$ on $\mathbb R$. An item with context $x$ and noise $\xi$ has valuation
--   $$u=v(x)+\xi,\qquad v(x)=\langle x,w^*\rangle-\mu^* .$$
--
--   The **constants** $\theta=(B,c_x,C_x,c_\xi,C_\xi)$ satisfy $0<c_x\le C_x$ and $0<c_\xi\le C_\xi$. The instance satisfies **Assumptions (A1)–(A3)** with these constants when
--
--   1. (A1) $\|w^*\|_2\le B$ and $|\mu^*|\le B$;
--   2. (A2) $P_X$ is supported on $B_2(d)$ and has a density $f_x$ with $c_xf_u(x)\le f_x(x)\le C_xf_u(x)$ for all $x\in B_2(d)$;
--   3. (A3) $\Pr[\xi\le 0]=\Pr[\xi\ge 0]=1/2$, and $P_\xi$ has a density $f_\xi$ with $\sup_\xi f_\xi(\xi)\le C_\xi/\|w^*\|_2$ and $\inf_{|\xi|\le 2}f_\xi(\xi)\ge c_\xi/\|w^*\|_2$.
--
--   Every statement of the mission is made for all instances satisfying these assumptions.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $P_U$ is Lebesgue measure conditioned on the closed ball. Densities are measurable $[0,\infty]$-valued functions; the bounds are required of one version of the density, so they hold up to null sets. Support on the ball is encoded by a density vanishing off the ball. Because Lean's $c/0$ is $0$, (A3) with $w^*=0$ would force $f_\xi\le 0$, which no probability density satisfies; so (A3) implies $w^*\neq 0$, as the source's division presupposes.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §1.2, p.7; §2, pp.7–8, Eq. (1), Assumptions (A1)–(A3); §4, p.16 (P_U)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace ActiveCtxSearch

/-- The context space `ℝᵈ` of Chen, Liu & Wang, *Active Learning for Contextual Search with Binary
Feedback*, arXiv:2110.01072v2, §2, p.7, with the Euclidean norm `‖·‖₂`.

**Formalization Note** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, so `‖x‖` is the `ℓ₂` norm and `⟪x, w⟫` the
standard inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The unit `ℓ₂` ball `B₂(d) = {x ∈ ℝᵈ : ‖x‖₂ ≤ 1}` (arXiv:2110.01072v2, (A2), p.8). -/
def unitBall (d : ℕ) : Set (E d) := Metric.closedBall 0 1

/-- The uniform distribution `P_U` on `B₂(d)` (arXiv:2110.01072v2, §4, p.16): Lebesgue measure on the
ball, normalized to total mass one. -/
noncomputable def PU (d : ℕ) : Measure (E d) := volume[|unitBall d]

/-- The density `f_u` of the uniform distribution on `B₂(d)` (arXiv:2110.01072v2, (A2), p.8): equal
to `1 / vol(B₂(d))` on the ball and to `0` outside it. -/
noncomputable def fu (d : ℕ) (x : E d) : ℝ≥0∞ :=
  (unitBall d).indicator (fun _ => (volume (unitBall d))⁻¹) x

/-- The problem-dependent constants `θ = (B, c_x, C_x, c_ξ, C_ξ)` of arXiv:2110.01072v2, §1.2, p.7
and (A1)–(A3), p.8, with `0 < c_x ≤ C_x` and `0 < c_ξ ≤ C_ξ` as required in (A2), (A3).

**Formalization Note** The finiteness `B < ∞` of (A1) is automatic for a real number. -/
structure Params where
  /-- The bound `B` of (A1). -/
  B : ℝ
  /-- The lower density ratio `c_x` of (A2). -/
  cx : ℝ
  /-- The upper density ratio `C_x` of (A2). -/
  Cx : ℝ
  /-- The lower noise-density constant `c_ξ` of (A3). -/
  cξ : ℝ
  /-- The upper noise-density constant `C_ξ` of (A3). -/
  Cξ : ℝ
  cx_pos : 0 < cx
  cx_le_Cx : cx ≤ Cx
  cξ_pos : 0 < cξ
  cξ_le_Cξ : cξ ≤ Cξ

/-- An instance of the contextual-search model of arXiv:2110.01072v2, §2, p.7, Eq. (1): the
coefficient vector `w* ∈ ℝᵈ`, the intercept `μ* ∈ ℝ`, the context distribution `P_X` on `ℝᵈ` and the
noise distribution `P_ξ` on `ℝ`. The valuation of an item with context `x` and noise `ξ` is
`u = v(x) + ξ = ⟨x, w*⟩ − μ* + ξ`. -/
structure Problem (d : ℕ) where
  /-- The coefficient vector `w*`. -/
  w : E d
  /-- The intercept `μ*`. -/
  μ : ℝ
  /-- The context distribution `P_X`. -/
  PX : Measure (E d)
  /-- The noise distribution `P_ξ`. -/
  Pξ : Measure ℝ
  [isProb_PX : IsProbabilityMeasure PX]
  [isProb_Pξ : IsProbabilityMeasure Pξ]

attribute [instance] Problem.isProb_PX Problem.isProb_Pξ

namespace Problem

variable {d : ℕ}

/-- The mean valuation `v(x) = ⟨x, w*⟩ − μ*` (arXiv:2110.01072v2, Eq. (1), p.7). -/
noncomputable def v (I : Problem d) (x : E d) : ℝ := ⟪x, I.w⟫ - I.μ

end Problem

/-- Assumptions (A1)–(A3) of arXiv:2110.01072v2, p.8, with the constants `θ`:

* (A1) `‖w*‖₂ ≤ B` and `|μ*| ≤ B`;
* (A2) `P_X` is supported on `B₂(d)` and has a density `f_x` with `c_x f_u ≤ f_x ≤ C_x f_u` on `B₂(d)`;
* (A3) `Pr[ξ ≤ 0] = Pr[ξ ≥ 0] = 1/2`, and `P_ξ` has a density `f_ξ` with `sup_ξ f_ξ(ξ) ≤ C_ξ/‖w*‖₂` and
  `inf_{|ξ| ≤ 2} f_ξ(ξ) ≥ c_ξ/‖w*‖₂`.

**Formalization Note** A density is a measurable `ℝ≥0∞`-valued function whose `withDensity` measure
is the distribution; the bounds are required of one version of it (so they are bounds up to null
sets, as for any density). Support on the ball is encoded by a density vanishing off the ball. In
(A3), `w* = 0` would make both bounds `0` (Lean's `c / 0 = 0`), which no probability density meets, so
(A3) implies `w* ≠ 0`, as the division in the source presupposes. -/
structure Assumptions {d : ℕ} (θ : Params) (I : Problem d) : Prop where
  A1_w : ‖I.w‖ ≤ θ.B
  A1_μ : |I.μ| ≤ θ.B
  A2 : ∃ fx : E d → ℝ≥0∞, Measurable fx ∧ I.PX = volume.withDensity fx ∧
    (∀ x, x ∉ unitBall d → fx x = 0) ∧
    ∀ x ∈ unitBall d, ENNReal.ofReal θ.cx * fu d x ≤ fx x ∧ fx x ≤ ENNReal.ofReal θ.Cx * fu d x
  A3_median : I.Pξ (Set.Iic 0) = 1 / 2 ∧ I.Pξ (Set.Ici 0) = 1 / 2
  A3_density : ∃ fξ : ℝ → ℝ≥0∞, Measurable fξ ∧ I.Pξ = volume.withDensity fξ ∧
    (∀ t, fξ t ≤ ENNReal.ofReal (θ.Cξ / ‖I.w‖)) ∧
    ∀ t, |t| ≤ 2 → ENNReal.ofReal (θ.cξ / ‖I.w‖) ≤ fξ t

end ActiveCtxSearch


