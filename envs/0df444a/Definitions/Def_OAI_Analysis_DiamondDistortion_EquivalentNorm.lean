-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
-- name    : OAI_Analysis_DiamondDistortion_EquivalentNorm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:22:13.888499+00:00
-- url     : https://prove2.me/theorems/3eceefd8-3029-4bee-bdd1-d828ee7e7f21
-- title:
--   Renorming by an equivalent seminorm, and coordinatewise maps between $\ell^p$ sequence spaces
-- statement:
--   This file provides two general tools: renorming a normed space by an equivalent seminorm, and applying a linearly bounded map coordinatewise to $\ell^p$ sequences.
--
--   1. **Equivalent-norm data.** Let $(E,\|\cdot\|)$ be a real normed space. An equivalent-norm datum on $E$ consists of a seminorm $N$ on $E$ and real constants $\alpha,\beta$ such that
--   $$\|v\|\le\alpha\,N(v)\qquad\text{and}\qquad N(v)\le\beta\,\|v\|\qquad\text{for all }v\in E.$$
--   The first inequality gives $N(v)=0\Rightarrow v=0$, so $N$ is a norm.
--   2. **The renormed space.** $E_N$ is the vector space $E$ equipped with the norm $N$; it is a real normed space. The identity map $E_N\to E$ is a linear equivalence and, by the two inequalities, a continuous linear equivalence (an isomorphism of normed spaces) whose underlying bijection is a uniform equivalence. Consequently, if $E$ is complete then so is $E_N$.
--   3. **Pointwise norms of $\ell^p$ families.** Fix an index set $\iota$ and an exponent $p\in[1,\infty]$. For a real normed space $E$ let $\ell^p(\iota;E)$ be the space of families $v=(v_i)_{i\in\iota}$ in $E$ with $\sum_i\|v_i\|^p<\infty$ (bounded families when $p=\infty$), normed by $\|v\|_p=\bigl(\sum_i\|v_i\|^p\bigr)^{1/p}$ (the supremum of $\|v_i\|$ when $p=\infty$). The family of norms $|v|=(\|v_i\|)_{i\in\iota}$ belongs to $\ell^p(\iota;\mathbb{R})$, and $\bigl\||v|\bigr\|_p=\|v\|_p$.
--   4. **Coordinatewise maps.** Let $E,F$ be real normed spaces, $C\ge0$, and $f:E\to F$ any map (not necessarily linear or continuous) with $\|f(x)\|\le C\|x\|$ for all $x\in E$. Then for every $v\in\ell^p(\iota;E)$ the family $f(v)=(f(v_i))_{i\in\iota}$ lies in $\ell^p(\iota;F)$ and
--   $$\|f(v)\|_p\le C\,\|v\|_p.$$
--
--   The first construction transports completeness, and any other property invariant under isomorphism, between a normed space and an equivalent renorming of it. The second builds maps between vector-valued $\ell^p$ sums out of norm-bounded maps between the summands, with the same bound.
--
--   **Formalization Note** The datum is `EquivalentNorm.Data E` with fields `seminorm`, `lowerConstant` ($\alpha$), `upperConstant` ($\beta$), `lower` and `upper`; no sign condition on the constants is imposed. `Data.Space` is the renormed copy, `of` is the identity map into it (with `norm_of`), `algebraEquiv`, `equiv` (built with `LinearEquiv.toContinuousLinearEquivOfBounds`) and `uniformEquiv` are the identifications with $E$, and a `CompleteSpace` instance is transferred along `uniformEquiv`. The $\ell^p$ spaces are Mathlib's `lp` with an extended exponent; `LpBoundedMap.normVector` and `LpBoundedMap.map` are the constructions of items 3 and 4, `map_apply` is their coordinate formula, and the norm statements `normVector_norm` and `map_norm` assume `Fact (1 ≤ p)` together with an explicit hypothesis `p ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/EquivalentNorm.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/EquivalentNorm.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace EquivalentNorm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  seminorm : Seminorm ℝ E
  lowerConstant : ℝ
  upperConstant : ℝ
  lower : ∀ v,‖v‖ ≤ lowerConstant*seminorm v
  upper : ∀ v,seminorm v ≤ upperConstant*‖v‖
namespace Data
variable (A : Data E)
lemma separates (v : E) (hv : A.seminorm v=0) : v=0 := by
  have hh := A.lower v
  rw [hv,mul_zero] at hh
  exact norm_le_zero_iff.mp hh

def Space (_A : Data E) := E
instance : AddCommGroup A.Space := inferInstanceAs (AddCommGroup E)
instance : Module ℝ A.Space := inferInstanceAs (Module ℝ E)
instance : NormedAddCommGroup A.Space := AddGroupNorm.toNormedAddCommGroup
  { A.seminorm.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := A.separates }
instance : NormedSpace ℝ A.Space where
  norm_smul_le t v := le_of_eq (A.seminorm.smul' t v)

def of (v : E) : A.Space := v
@[simp] lemma norm_of (v : E) : ‖A.of v‖=A.seminorm v := rfl

def algebraEquiv : A.Space ≃ₗ[ℝ] E := { LinearEquiv.refl ℝ E with }
def equiv : A.Space ≃L[ℝ] E :=
  A.algebraEquiv.toContinuousLinearEquivOfBounds A.lowerConstant A.upperConstant A.lower A.upper
def uniformEquiv : A.Space ≃ᵤ E where
  toEquiv := A.equiv.toEquiv
  uniformContinuous_toFun := A.equiv.toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun := A.equiv.symm.toContinuousLinearMap.uniformContinuous
instance [CompleteSpace E] : CompleteSpace A.Space :=
  A.uniformEquiv.completeSpace_iff.mpr inferInstance
end Data
end EquivalentNorm

namespace PathModel
open RecursiveModel
end PathModel

namespace CoordinateCompletion.Data
variable {ι E : Type*} (A : CoordinateCompletion.Data ι)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end CoordinateCompletion.Data

namespace RecursiveModel
variable {E : ℕ → Type*} [∀ h,NormedAddCommGroup (E h)] [∀ h,NormedSpace ℝ (E h)]
end RecursiveModel

namespace FiniteLpDensity
variable {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)]
open RecursiveModel
end FiniteLpDensity

namespace EquivalentNorm.Data
open RecursiveModel
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : EquivalentNorm.Data (lp (fun _ : ι => ℝ) p))
end EquivalentNorm.Data

namespace PathModel
open RecursiveModel
end PathModel

namespace LpBoundedMap
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
def normVector (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => ℝ) p :=
  ⟨fun i => ‖v i‖,v.property.norm⟩
lemma normVector_norm {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (v : lp (fun _ : ι => E) p) : ‖normVector v‖=‖v‖ := by
  have he (i : ι) : ‖normVector v i‖=‖v i‖ := norm_norm _
  exact le_antisymm (lp.norm_mono hp (fun i => (he i).le)) (lp.norm_mono hp (fun i => (he i).ge))
def map (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => F) p :=
  ⟨fun i => f (v i),(C • normVector v).property.mono' (fun i => by
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
      normVector,abs_norm] using hf (v i))⟩
lemma map_apply {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) (i : ι) : map f C hC hf v i=f (v i) := rfl
lemma map_norm {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : ‖map f C hC hf v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖C • normVector v‖ := lp.norm_mono hp (fun i => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
        normVector,abs_norm,map_apply] using hf (v i))
    _ = C*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,normVector_norm hp]
end LpBoundedMap

end DiamondDistortion

end

end OAI


