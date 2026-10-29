-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_FluidLimits
-- name    : BramsonQueueing_Fluid_FluidLimits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:00.274597+00:00
-- url     : https://prove2.me/theorems/c6551367-f749-4ac9-a4b0-fce76aee306a
-- title:
--   Admissible fluid scaling, association, and residual-limit assertions
-- statement:
--   An admissible sequence consists of positive scales $a_n\to\infty$ and initial states $x_n$, with bounded $|z_n|/a_n$ and vanishing $|u_n|/a_n,|v_n|/a_n$. A fluid limit is a simultaneous uniform-on-compact limit of all six paths $\mathcal X^{x_n}(a_nt)/a_n$, for some $\omega\in G$ and some admissible sequence. Stability uses one draining coefficient for every such limit. A fluid model is associated with the network when every admissible sequence, at every sample in $G$, has a strictly increasing subsequence whose scaled paths converge to a solution of that model.
--   The residual-conclusions predicate packages precisely (4.91)–(4.93): the two uniform expectation bounds over $t\ge1,|x|\le t$, and one $c_0\ge1$ such that for every $c\ge c_0$ both residual masses divided by $|x|$ vanish on $G$ and in expectation as $|x|\to\infty$. Uniform bounds use one finite constant, equivalently the maximum of the source's two finite suprema. The source's second denominator in (4.93) is read as $|x|$, as confirmed by its proof.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Section 4.3, printed 111–113 / PDF 119–121, equations (4.71)–(4.73); Proposition 4.15, printed 119 / PDF 127.

import Definitions.Def_BramsonQueueing_Fluid_HLNetwork

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

variable {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
  [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- (4.71): scaling diverges, initial queue mass is bounded after scaling,
and both residual masses vanish after scaling. -/
def AdmissibleScaling (n : HLNetwork d S Ω) (a : ℕ → ℝ≥0) (x : ℕ → S) : Prop :=
  (∀ i, 0 < a i) ∧ Tendsto a atTop atTop ∧
  (∃ B : ℝ, ∀ i, (n.zMass (x i) : ℝ) / a i ≤ B) ∧
  Tendsto (fun i => (n.uMass (x i) : ℝ) / a i) atTop (𝓝 0) ∧
  Tendsto (fun i => (n.vMass (x i) : ℝ) / a i) atTop (𝓝 0)

def IsFluidLimit (n : HLNetwork d S Ω) (q : SixPath K J) : Prop :=
  ∃ ω, PrimitiveGood n.primitives ω ∧ ∃ a x,
    AdmissibleScaling n a x ∧ SixUOC (fun i => scaleSix (a i) (n.path (x i) ω)) q

def FluidLimitsStable (n : HLNetwork d S Ω) : Prop := StableFamily (IsFluidLimit n)

/-- Association includes subsequence existence for every admissible sequence,
as required on printed p.112; it is not just a vacuous implication about limits. -/
def Associated (n : HLNetwork d S Ω) (model : FluidModel d) : Prop :=
  ∀ ω, PrimitiveGood n.primitives ω → ∀ a x, AdmissibleScaling n a x →
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ q : SixPath K J,
      SixUOC (fun i => scaleSix (a (r i)) (n.path (x (r i)) ω)) q ∧ model.Solution q

/-- Convergence to zero as the full state size tends to infinity. -/
def VanishesAtLargeStates (n : HLNetwork d S Ω) (f : S → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ R : ℝ≥0, ∀ x, R ≤ n.size x → f x ≤ ε

/-- The complete residual-time conclusions (4.91)–(4.93), with a single c₀. -/
def ResidualConclusions (n : HLNetwork d S Ω) : Prop :=
  (∃ C : ℝ≥0, ∀ t : ℝ≥0, 1 ≤ t → ∀ x, n.size x ≤ t →
    (∫⁻ ω, (n.uMass (n.process.X x t ω) : ℝ≥0∞) ∂n.μ) / t ≤ C ∧
    (∫⁻ ω, (n.vMass (n.process.X x t ω) : ℝ≥0∞) ∂n.μ) / t ≤ C) ∧
  ∃ c₀ : ℝ≥0, 1 ≤ c₀ ∧ ∀ c ≥ c₀,
    (∀ ω, PrimitiveGood n.primitives ω →
      VanishesAtLargeStates n (fun x =>
        (n.uMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) / n.size x) ∧
      VanishesAtLargeStates n (fun x =>
        (n.vMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) / n.size x)) ∧
    VanishesAtLargeStates n (fun x =>
      (∫⁻ ω, (n.uMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) ∂n.μ) / n.size x) ∧
    VanishesAtLargeStates n (fun x =>
      (∫⁻ ω, (n.vMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) ∂n.μ) / n.size x)

end BramsonQueueing.Fluid


