-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Operations
-- name    : OAI_Analysis_C0Absorption_Operations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:10:45.20483+00:00
-- url     : https://prove2.me/theorems/f0f4c599-6ccf-4259-a941-e15194217d3b
-- title:
--   Signed bounds, remainder operations and sub-representations
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes.
--
--   1. **Signed bounds.** A sequence $(m_n)$ in a normed space has signed bound $M$ if every finite signed sum of distinct terms is bounded:
--   $$
--   \Bigl\|\sum_{i=1}^n\pm m_{\iota(i)}\Bigr\|\le M\qquad\text{for all injective }\iota\text{ and signs}.
--   $$
--   This is the behaviour of the unit vector basis of $c_0$, and it is what a linear copy of $c_0$ would force.
--   2. **Remainders.** The remainder of a cylinder operation has the same scale and centre but acts by $R_{q,\varepsilon}u=\mathrm{cutoff}\cdot(u(q)-u)$ instead of the flattening $G_{q,\varepsilon}$. The remainder of a tail operation replaces the factor by the factor minus $1$.
--   3. **Sub-representations.** A sublist of the operations of a generated representation, or a list with the same scales, is again a generated representation, since ordering and budget are inherited. Tail products are multiplicative under concatenation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Operations.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Operations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def SignedBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ) : Prop :=
  ∀ n (ι : Fin n → ℕ), Function.Injective ι → ∀ ε : Fin n → Bool,
    ‖∑ i, realSign (ε i) • m (ι i)‖ ≤ M

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

end SignedBound

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}

def remainder (op : CylinderOperation I) : CylinderOperation I := {op with isG := false}
@[simp] theorem remainder_scale (op : CylinderOperation I) : op.remainder.scale=op.scale := rfl
@[simp] theorem remainder_point (op : CylinderOperation I) : op.remainder.point=op.point := rfl
@[simp] theorem remainder_act (op : CylinderOperation I) (u : Cube I → ℝ) :
    op.remainder.act u = localR op.point op.scale u := rfl

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def subrepresentation (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (ho : ops.Sublist r.operations) : GeneratedRepresentation B γ where
  operations := ops
  ordered := r.ordered.sublist ho
  budget := lt_of_le_of_lt ((ho.map CylinderOperation.scale).sum_le_sum (by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact p.scale_pos.le)) r.budget

def sameScales (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (hs : ops.map CylinderOperation.scale = r.operations.map CylinderOperation.scale) :
    GeneratedRepresentation B γ where
  operations := ops
  ordered := by
    apply (List.pairwise_map (R := fun a b : ℝ => b ≤ a)).mp
    rw [hs]
    exact List.pairwise_map.mpr r.ordered
  budget := by rw [hs]; exact r.budget

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
@[ext] theorem ext' {a b : TailOperation} (hs : a.scaleIndex=b.scaleIndex)
    (hn : a.tailIndex=b.tailIndex) (hg : a.isBasic=b.isBasic) : a=b := by
  cases a; cases b; simp_all

def remainder (t : TailOperation) : TailOperation := {t with isBasic := false}
@[simp] theorem remainder_scaleIndex (t : TailOperation) : t.remainder.scaleIndex=t.scaleIndex := rfl
@[simp] theorem remainder_tailIndex (t : TailOperation) : t.remainder.tailIndex=t.tailIndex := rfl
@[simp] theorem remainder_isBasic (t : TailOperation) : t.remainder.isBasic=false := rfl

end TailOperation

@[simp] theorem tailProduct_append (pre post : List TailOperation) (s : C0Ball) :
    tailProduct (pre++post) s = tailProduct pre s*tailProduct post s := by
  simp only [tailProduct,List.map_append,List.prod_append]

end
end C0Absorption

end OAI


