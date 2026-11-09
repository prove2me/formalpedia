-- Prove2me | Definitions.Def_ConsumerMenuComplexity_Independent_Mechanisms
-- name    : ConsumerMenuComplexity_Independent_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:57:11.339532+00:00
-- url     : https://prove2.me/theorems/09675d59-87e0-4a2a-bf0a-b8e569cf96b7
-- title:
--   §§2–3 — unit-demand mechanisms, menus, support complexity and actual objectives
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   For caps $\alpha\in[0,1]^2$, feasibility means $a_i^D(M)\le\alpha_i$. Utility optimality means feasibility and $U_D(N)\le U_D(M)$ for every feasible admissible competitor $N$. Lagrangian optimality compares $L$ against every admissible competitor, with no restriction to structured menus. Structured optimality instead compares exactly the menus satisfying S1 (each option allocates at most one item) and S2 (the only option allocating item 2 is $(0,d,0)$), at the specified $d\in[0,1]$.
--
--   The non-null selected option set is
--   $$\{(x_1^M(v),x_2^M(v),p^M(v)):v\in\operatorname{support}(D)\}\setminus\{(0,0,0)\}.$$
--   Support is topological support: every open neighborhood has positive prior mass. Infinite menu complexity means this set is infinite, including options selected only by measure-zero support types. The product prior is the pushforward of the product of the two marginal laws under the coordinate pairing map.
--
--   These definitions separate operational feasibility, stochastic objectives and the complexity quantity shared by the mission. Extended nonnegative utility expectation preserves infinite utility, while the bounded allocation costs are real numbers.
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, §§2–3, PDF pp. 6–10 (printed pp. 5–9), especially §2.1 and footnote 5 on PDF p.8

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped ENNReal NNReal

namespace ConsumerMenuComplexity.Independent

abbrev TypeSpace := Fin 2 → ℝ≥0
abbrev Mechanism := MultiItemRev.BundlingOpt.Mechanism (Fin 2)
abbrev Option := (Fin 2 → ℝ) × ℝ

def utility (M : Mechanism) : TypeSpace → ℝ :=
  MultiItemRev.BundlingOpt.buyerPayoff M

def typeAt (a b : ℝ≥0) : TypeSpace := ![a, b]

def option (a b p : ℝ) : Option := (![a, b], p)

def nullOption : Option := option 0 0 0

def selected (M : Mechanism) (v : TypeSpace) : Option := (M.q v, M.s v)

def optionUtility (o : Option) (v : TypeSpace) : ℝ :=
  ∑ i, o.1 i * (v i : ℝ) - o.2

/-- All-report truthfulness, participation and unit-demand feasibility (§2). -/
def Admissible (M : Mechanism) : Prop :=
  MultiItemRev.BundlingOpt.IsFeasible M ∧
  (∀ v, M.q v 0 + M.q v 1 ≤ 1) ∧
  MultiItemRev.BundlingOpt.IsIC M ∧
  MultiItemRev.BundlingOpt.IsIR M ∧
  MultiItemRev.BundlingOpt.IsNPT M ∧ Measurable M.q ∧ Measurable M.s

def ValidOption (o : Option) : Prop :=
  (∀ i, 0 ≤ o.1 i ∧ o.1 i ≤ 1) ∧ o.1 0 + o.1 1 ≤ 1 ∧ 0 ≤ o.2

def ValidMenu (S : Set Option) : Prop :=
  nullOption ∈ S ∧ ∀ o ∈ S, ValidOption o

/-- An actual maximizing selection at every type; no unattained supremum default. -/
def Selects (S : Set Option) (M : Mechanism) : Prop :=
  ∀ v, selected M v ∈ S ∧ ∀ o ∈ S, optionUtility o v ≤ utility M v

def offered (M : Mechanism) : Set Option := Set.range (selected M) ∪ {nullOption}

def OnlySingleItem (S : Set Option) : Prop :=
  ∀ o ∈ S, o.1 0 = 0 ∨ o.1 1 = 0

/-- S2 includes the zero-lottery edge case; the only item-2 option is (0,d,0). -/
def Structured (S : Set Option) (d : ℝ) : Prop :=
  0 ≤ d ∧ d ≤ 1 ∧ OnlySingleItem S ∧ option 0 d 0 ∈ S ∧
    ∀ o ∈ S, o.1 1 ≠ 0 → o = option 0 d 0

/-- Topological support of the actual prior on the whole orthant. -/
def priorSupport (μ : Measure TypeSpace) : Set TypeSpace :=
  {v | ∀ U : Set TypeSpace, IsOpen U → v ∈ U → μ U ≠ 0}

def nonNullOptions (μ : Measure TypeSpace) (M : Mechanism) : Set Option :=
  selected M '' priorSupport μ \ {nullOption}

noncomputable def productLaw (D₁ D₂ : Measure ℝ≥0) : Measure TypeSpace :=
  (D₁.prod D₂).map (fun v => typeAt v.1 v.2)

/-- Nonnegative extended expectation: admissible utilities never have a negative part. -/
noncomputable def expectedUtility (μ : Measure TypeSpace) (M : Mechanism) : EReal :=
  (∫⁻ v, ENNReal.ofReal (utility M v) ∂μ : ℝ≥0∞)

/-- Used only for probability priors and admissible (hence bounded) allocations. -/
noncomputable def supply (μ : Measure TypeSpace) (M : Mechanism) (i : Fin 2) : ℝ :=
  ∫ v, M.q v i ∂μ

/-- A bounded real allocation cost is subtracted from extended utility. -/
noncomputable def lagrangian (μ : Measure TypeSpace) (cost : Fin 2 → ℝ)
    (M : Mechanism) : EReal :=
  expectedUtility μ M - ((cost 0 * supply μ M 0 + cost 1 * supply μ M 1 : ℝ) : EReal)

def ValidCaps (α : Fin 2 → ℝ) : Prop := ∀ i, 0 ≤ α i ∧ α i ≤ 1

def MeetsCaps (μ : Measure TypeSpace) (α : Fin 2 → ℝ) (M : Mechanism) : Prop :=
  ∀ i, supply μ M i ≤ α i

def UtilityOptimal (μ : Measure TypeSpace) (α : Fin 2 → ℝ) (M : Mechanism) : Prop :=
  Admissible M ∧ MeetsCaps μ α M ∧
    ∀ N, Admissible N → MeetsCaps μ α N → expectedUtility μ N ≤ expectedUtility μ M

def LOptimal (μ : Measure TypeSpace) (cost : Fin 2 → ℝ) (M : Mechanism) : Prop :=
  Admissible M ∧ ∀ N, Admissible N → lagrangian μ cost N ≤ lagrangian μ cost M

def StructuredOptimal (μ : Measure TypeSpace) (c d : ℝ)
    (S : Set Option) (M : Mechanism) : Prop :=
  ValidMenu S ∧ Admissible M ∧ Selects S M ∧ Structured S d ∧
    ∀ T N, ValidMenu T → Admissible N → Selects T N → Structured T d →
      lagrangian μ ![1, c] N ≤ lagrangian μ ![1, c] M

end ConsumerMenuComplexity.Independent


