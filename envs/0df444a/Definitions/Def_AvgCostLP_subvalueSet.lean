-- Prove2me | Definitions.Def_AvgCostLP_subvalueSet
-- name    : AvgCostLP_subvalueSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:29.385739+00:00
-- url     : https://prove2.me/theorems/ef2f5ee5-7724-48c5-98ef-bec14281b8ee
-- title:
--   (5.1) — the set $H\subset\mathbb R\times\mathbb M(\mathbb X)\times\mathbb R$ and the subvalue $\underline\rho$ of (P)
-- statement:
--   For the programs (3.10)–(3.11), the linear map is $L=(L_0,L_1)$ with $L_0\gamma=\gamma(\Gamma)$ and $(L_1\gamma)(B)=\hat\gamma(B)-\int_\Gamma q(B\mid x,a)\,\gamma(d(x,a))$ (3.6)–(3.7), and
--   $$H:=\big\{(L\gamma,\ \langle\gamma,c\rangle+r)\ \big|\ \gamma\in\mathbb M^+_w(\Gamma),\ r\ge0\big\}\subset\mathbb R\times\mathbb M(\mathbb X)\times\mathbb R, \tag{5.1}$$
--   where $\mathbb M(\mathbb X)$ is the space of finite signed Borel measures. $\overline H$ is its closure in $\sigma(\mathbb R\times\mathbb M(\mathbb X)\times\mathbb R,\ \mathbb R\times\mathbb F_b(\mathbb X)\times\mathbb R)$, with the pairing $\langle(s,\zeta,t),(\rho,h,r)\rangle=s\rho+\int h\,d\zeta+tr$. The **subvalue** of (P) is
--   $$\underline\rho:=\inf\{r\mid((1,0),r)\in\overline H\}.$$
--   `subvalueSet` is the set $\{r\mid((1,0),r)\in\overline H\}$.
--
--   **Formalization Note** $\mathbb M(\mathbb X)$ is Mathlib's `SignedMeasure`; $\int h\,d\zeta$ is defined through the Jordan decomposition. The weak topology is the coarsest making every pairing with $\mathbb R\times\mathbb F_b(\mathbb X)\times\mathbb R$ continuous.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, (3.6)-(3.8) p.11, §5.1.1 and (5.1), p.20

import Mathlib
import Definitions.Def_AvgCostLP_Model
import Definitions.Def_AvgCostLP_IsDualFeasible

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- Yu, arXiv:1905.12095v3, §3.1, p.10: `F_b(X)`, the bounded Borel measurable real-valued
functions on `X`. -/
def Fb (X : Type*) [MeasurableSpace X] : Type _ :=
  {h : X → ℝ // IsBoundedBorel h}

/-- `∫_X h dζ` for a finite signed Borel measure `ζ ∈ M(X)` (p.10), defined through the Jordan
decomposition `ζ = ζ⁺ − ζ⁻`: `∫ h dζ := ∫ h dζ⁺ − ∫ h dζ⁻`. -/
noncomputable def signedIntegral (h : X → ℝ) (ζ : SignedMeasure X) : ℝ :=
  ∫ x, h x ∂ζ.toJordanDecomposition.posPart - ∫ x, h x ∂ζ.toJordanDecomposition.negPart

/-- The bilinear form of the dual pair `(ℝ × M(X) × ℝ, ℝ × F_b(X) × ℝ)` (pp.10, 20):
`⟨(s, ζ, t), (ρ, h, r)⟩ = s ρ + ∫_X h dζ + t r`, the pairing `⟨(r, ζ), (ρ, h)⟩ = rρ + ∫ h dζ` of
p.10 extended by the product of the last coordinates, as in (2.4). -/
noncomputable def pairing (z : ℝ × SignedMeasure X × ℝ) (w : ℝ × Fb X × ℝ) : ℝ :=
  z.1 * w.1 + signedIntegral w.2.1.1 z.2.1 + z.2.2 * w.2.2

/-- The weak topology `σ(ℝ × M(X) × ℝ, ℝ × F_b(X) × ℝ)` (p.20): the coarsest topology on
`ℝ × M(X) × ℝ` making every map `z ↦ ⟨z, w⟩` continuous.

**Formalization Note** `M(X)`, the finite signed Borel measures, is Mathlib's `SignedMeasure X`
(real-valued, hence finite). -/
@[reducible] noncomputable def weakTop : TopologicalSpace (ℝ × SignedMeasure X × ℝ) :=
  TopologicalSpace.induced (fun z : ℝ × SignedMeasure X × ℝ => fun w : ℝ × Fb X × ℝ => pairing z w)
    Pi.topologicalSpace

/-- Yu, arXiv:1905.12095v3, (3.6)–(3.7), p.11: the second component of `Lγ`,
`(L₁γ)(B) = γ̂(B) − ∫_Γ q(B | x, a) γ(d(x, a))`, as a finite signed measure on `X`. -/
noncomputable def L1 (M : Model X A) (γ : FiniteMeasure (X × A)) : SignedMeasure X :=
  ((γ : Measure (X × A)).map Prod.fst).toSignedMeasure - (M.q ∘ₘ (γ : Measure (X × A))).toSignedMeasure

/-- Yu, arXiv:1905.12095v3, (5.1), p.20 (the set `H` of (2.4) for the programs (3.10)–(3.11)):
`H := {(Lγ, ⟨γ, c⟩ + r) | γ ∈ M⁺_w(Γ), r ≥ 0} ⊂ ℝ × M(X) × ℝ`, with `Lγ = (γ(Γ), L₁γ)`.

**Formalization Note** `γ ∈ M⁺_w(Γ)` is a finite nonnegative measure on `X × A` concentrated on
`Γ` with `∫ w dγ < ∞`, `w = 1 + c`; then `⟨γ, c⟩ = ∫ c dγ` is finite and is taken as a real
number. -/
def setH (M : Model X A) : Set (ℝ × SignedMeasure X × ℝ) :=
  {z | ∃ γ : FiniteMeasure (X × A), (γ : Measure (X × A)) M.graphᶜ = 0 ∧
    ∫⁻ p, (1 + M.c p) ∂(γ : Measure (X × A)) < ⊤ ∧ ∃ r : ℝ, 0 ≤ r ∧
      z = (((γ : Measure (X × A)) M.graph).toReal, L1 M γ,
        (∫⁻ p, M.c p ∂(γ : Measure (X × A))).toReal + r)}

/-- Yu, arXiv:1905.12095v3, p.20: `{r | ((1, 0), r) ∈ H̄}`, where `H̄` is the closure of `H` in
`σ(ℝ × M(X) × ℝ, ℝ × F_b(X) × ℝ)`. Its infimum is the subvalue `ρ̲` of (P). -/
def subvalueSet (M : Model X A) : Set ℝ :=
  {r | ((1, 0, r) : ℝ × SignedMeasure X × ℝ) ∈ @closure _ weakTop (setH M)}

end AvgCostLP


