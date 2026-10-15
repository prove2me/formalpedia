-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
-- name    : OAI_Combinatorics_BooleanFunctions_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:02.805281+00:00
-- url     : https://prove2.me/theorems/c7281b08-0126-4d38-8c5a-37b38016eb7e
-- title:
--   Product weights, random Boolean tables, and the table event of a selector
-- statement:
--   All index and value sets are finite where sums over them occur. The weights below are arbitrary real numbers; they are probability distributions when they are nonnegative and sum to one.
--
--   1. **Product weight.** For a family $p_i:\Lambda\to\mathbb{R}$ ($i\in I$) and $x\in\Lambda^I$, $P_p(x)=\prod_{i\in I}p_i(x_i)$, the weight of $x$ when the coordinates are independent with marginals $p_i$.
--   2. **Bernoulli weight.** $\mathrm{Ber}_p(\mathrm{true})=p$ and $\mathrm{Ber}_p(\mathrm{false})=1-p$.
--   3. **Leaf-table weight.** For $p:\Lambda\to\mathbb{R}$ and a Boolean table $\tau:\Lambda\to\mathbb{B}$, $\mathrm{LW}_p(\tau)=\prod_{a\in\Lambda}\mathrm{Ber}_{p(a)}(\tau(a))$: a random table with independent entries, $\tau(a)=\mathrm{true}$ with probability $p(a)$.
--   4. **Table weight.** For selector weights $s_i:B\to\mathbb{R}$ and leaf weights $w_i:B\to\mathbb{R}$ ($i\in I$), a selector table $\Sigma:B\to I$ together with leaf tables $L_i:B\to\mathbb{B}$ has weight
--   $$\mathrm{TW}_{s,w}(\Sigma,L)=\prod_{b\in B}s_{\Sigma(b)}(b)\;\prod_{i\in I}\mathrm{LW}_{w_i}(L_i).$$
--   5. **Bit.** $\mathrm{bit}(\mathrm{true})=1$ and $\mathrm{bit}(\mathrm{false})=0$.
--   6. **Table event.** For tables $(\Sigma,L)$ and labels $(y_0,(y_i)_{i\in I})\in B\times B^I$, the event holds if and only if
--   $$L_{\Sigma(y_0)}\big(y_{\Sigma(y_0)}\big)=\mathrm{false}\qquad\text{and}\qquad L_i(y_i)=\mathrm{true}\ \text{ for all } i\neq\Sigma(y_0).$$
--
--   The file proves the basic identities: if every $p_i$ sums to $1$ then $\sum_xP_p(x)=1$; $\sum_xP_p(x)\prod_if_i(x_i)=\prod_i\sum_ap_i(a)f_i(a)$; under the same normalization $\sum_xP_p(x)\,g(x_j)=\sum_ap_j(a)\,g(a)$; $\sum_b\mathrm{Ber}_p(b)=1$ and $\sum_b\mathrm{Ber}_p(b)\,\mathrm{bit}(b)=p$; and $\sum_\tau\mathrm{LW}_p(\tau)=1$ and $\sum_\tau\mathrm{LW}_p(\tau)\,\mathrm{bit}(\tau(a))=p(a)$.
--
--   The table event is the deterministic version of the soft event: the selector table reads the label $y_0$ and names a leaf, which must fail its table test while all other leaves pass. When the selector weights sum to one, averaging its indicator over random tables with weight $\mathrm{TW}_{s,w}$ recovers the soft weight, so some deterministic choice of tables does at least as well as the soft event; this is how continuous tests are rounded to deterministic finite observations.
--
--   **Formalization Note** The Lean names are `FiniteRounding.productWeight`, `sum_productWeight`, `weighted_product`, `weighted_evaluation`, `bernoulliWeight`, `bernoulli_sum`, `bernoulli_expect`, `leafWeight`, `leafWeight_sum`, `leafWeight_eval`, and `TableRounding.tableWeight`, `bit` and `tableEvent` (a proposition). In `bernoulli_expect` and `leafWeight_eval` the bit is written as `if b then 1 else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Rounding.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Rounding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SquareRootDegree
namespace FiniteRounding

/-- Real-valued finite probabilities; used only to select a deterministic finite table. -/
def productWeight {ι α : Type*} [Fintype ι] (p : ι → α → ℝ) (x : ι → α) : ℝ :=
  ∏ i, p i (x i)

theorem sum_productWeight {ι α : Type*} [Fintype ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ x, productWeight p x = 1 := by
  classical
  simp only [productWeight]
  rw [← Fintype.prod_sum]
  simp [hp]

theorem weighted_product {ι α : Type*} [Fintype ι] [Fintype α]
    (p f : ι → α → ℝ) :
    ∑ x, productWeight p x * ∏ i, f i (x i) = ∏ i, ∑ a, p i a * f i a := by
  classical
  simp only [productWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => p i a * f i a)).symm

theorem weighted_evaluation {ι α : Type*} [Fintype ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (j : ι) (g : α → ℝ) :
    ∑ x, productWeight p x * g (x j) = ∑ a, p j a * g a := by
  classical
  have h := weighted_product p (fun i a => if i = j then g a else 1)
  simpa [Finset.prod_ite_eq, hp] using h

def bernoulliWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

@[simp] theorem bernoulli_sum (p : ℝ) : ∑ b, bernoulliWeight p b = 1 := by
  simp [bernoulliWeight]

@[simp] theorem bernoulli_expect (p : ℝ) :
    ∑ b, bernoulliWeight p b * (if b then (1:ℝ) else 0) = p := by
  simp [bernoulliWeight]

/-- A distribution over entire leaf-test tables, not random bits added to the cube. -/
def leafWeight {α : Type*} [Fintype α] (p : α → ℝ) (t : α → Bool) : ℝ :=
  productWeight (fun a => bernoulliWeight (p a)) t

@[simp] theorem leafWeight_sum {α : Type*} [Fintype α] (p : α → ℝ) :
    ∑ t, leafWeight p t = 1 := sum_productWeight _ (fun _ => bernoulli_sum _)

@[simp] theorem leafWeight_eval {α : Type*} [Fintype α] (p : α → ℝ) (a : α) :
    ∑ t, leafWeight p t * (if t a then (1:ℝ) else 0) = p a := by
  simp only [leafWeight]
  simpa [bernoulliWeight] using weighted_evaluation (fun x => bernoulliWeight (p x))
    (fun _ => bernoulli_sum _) a (fun b => if b then (1 : ℝ) else 0)

end FiniteRounding
end SquareRootDegree

namespace SquareRootDegree
namespace TableRounding
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

def tableWeight (s w : ι → β → ℝ) (t : (β → ι) × (ι → β → Bool)) : ℝ :=
  productWeight (fun b i => s i b) t.1 * productWeight (fun i => leafWeight (w i)) t.2

def bit (b : Bool) : ℝ := if b then 1 else 0

def tableEvent (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) : Prop :=
  L (S x.1) (x.2 (S x.1)) = false ∧ ∀ i, i ≠ S x.1 → L i (x.2 i) = true

end TableRounding
end SquareRootDegree

end

end OAI


