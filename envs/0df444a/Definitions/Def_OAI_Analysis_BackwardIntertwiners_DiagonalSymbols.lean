-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_DiagonalSymbols
-- name    : OAI_Analysis_BackwardIntertwiners_DiagonalSymbols
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:07:31.421976+00:00
-- url     : https://prove2.me/theorems/e1fa5e32-8b7d-4dca-9536-d1751cb2f7ba
-- title:
--   Bounded measurable diagonal symbols over $\mathbb{Z}_2\times\mathbb{Z}$ and their fibrewise diagonal operators on $\ell^2(\mathbb{Z})$
-- statement:
--   Throughout, $\Omega$ denotes the ring $\mathbb{Z}_2$ of $2$-adic integers equipped with the completion of its normalized Haar probability measure $\mu$ (so "measurable" refers to the $\mu$-completed Borel $\sigma$-algebra), and $\ell^2(\mathbb{Z})$ is the Hilbert space of square-summable complex sequences $v=(v_j)_{j\in\mathbb{Z}}$ with standard basis vectors $e_j$. A *symbol* is a function $a:\Omega\times\mathbb{Z}\to\mathbb{C}$, $(x,j)\mapsto a(x,j)$. Symbols form a commutative unital $*$-algebra under pointwise addition, multiplication and complex scalar multiplication, with pointwise complex conjugation $a^*(x,j)=\overline{a(x,j)}$ as involution.
--
--   1. **Diagonal symbols.** The set
--   $$\mathcal D=\Bigl\{a:\Omega\times\mathbb{Z}\to\mathbb{C}\ :\ x\mapsto a(x,j)\ \text{is measurable for every } j\in\mathbb{Z},\ \ \sup_{x\in\Omega,\ j\in\mathbb{Z}}|a(x,j)|<\infty\Bigr\}$$
--   of measurable, uniformly bounded symbols is a unital $*$-subalgebra: it contains the constant symbols and is closed under sums, products, complex scalar multiples and conjugation. All operations on $\mathcal D$ are pointwise; for instance $(ab)(x,j)=a(x,j)\,b(x,j)$, $(a-b)(x,j)=a(x,j)-b(x,j)$, $a^*(x,j)=\overline{a(x,j)}$ and $a^n(x,j)=a(x,j)^n$.
--   2. **A chosen bound.** Every $a\in\mathcal D$ carries a fixed constant $C_a\ge0$ with
--   $$|a(x,j)|\le C_a\qquad\text{for all }x\in\Omega,\ j\in\mathbb{Z}.$$
--   3. **Fibre operators.** For $a\in\mathcal D$ and $x\in\Omega$, the diagonal operator $D_a(x):\ell^2(\mathbb{Z})\to\ell^2(\mathbb{Z})$ is
--   $$\bigl(D_a(x)v\bigr)_j=a(x,j)\,v_j\qquad(v\in\ell^2(\mathbb{Z}),\ j\in\mathbb{Z}),$$
--   a bounded complex-linear operator of norm at most $C_a$.
--
--   A diagonal symbol thus describes an operator field $x\mapsto D_a(x)$ that is diagonal in the standard basis of every fibre $\ell^2(\mathbb{Z})$, depends measurably on $x$ and is uniformly bounded; such fields define bounded decomposable operators on $L^2(\Omega,\mu;\ell^2(\mathbb{Z}))$. Because the algebra operations are pointwise, sums, products and conjugates of symbols correspond to sums, products and adjoints of the fibre operators, so polynomial expressions in a few basic symbols (shifted weight sequences, indicator functions) produce diagonal operators with explicitly known entries.
--
--   **Formalization Note** $\mathcal D$ is `diagonalSymbols`, a `StarSubalgebra` of the complex algebra of functions `Base → ℤ → ℂ`, and `DiagonalSymbol` is its subtype, coerced to functions. `Base` is $\mathbb{Z}_2$ with the null-measurable (completed) $\sigma$-algebra of the Haar measure. The constant $C_a$ is `a.bound`; it is extracted by choice from the membership proof, so it is some admissible bound and not necessarily the supremum of $|a|$ (`bound_nonneg`, `norm_le_bound`). The simp lemmas `zero_apply`, `one_apply`, `add_apply`, `mul_apply`, `sub_apply`, `star_apply`, `smul_apply`, `algebraMap_apply` and `pow_apply` are the pointwise formulas. $D_a(x)$ is `diagonalFiber a x`, built from the general fibre multiplier with bound $C_a$, and `diagonalFiber_apply` is its coordinate formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/DiagonalSymbols.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/DiagonalSymbols.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_OrdinaryStructure

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

def diagonalSymbols : StarSubalgebra ℂ (Base → ℤ → ℂ) where
  carrier := {a | (∀ j, Measurable (fun x => a x j)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x j, ‖a x j‖ ≤ C}
  zero_mem' := ⟨fun _ => measurable_const, 0, le_rfl, by simp⟩
  one_mem' := ⟨fun _ => measurable_const, 1, zero_le_one, by simp⟩
  add_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    exact ⟨fun j => (ha j).add (hb j), C+D, add_nonneg hC hD,
      fun x j => (norm_add_le _ _).trans (add_le_add (hCa x j) (hDb x j))⟩
  mul_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    refine ⟨fun j => (ha j).mul (hb j), C*D, mul_nonneg hC hD, fun x j => ?_⟩
    change ‖a x j * b x j‖ ≤ C*D
    rw [norm_mul]
    exact mul_le_mul (hCa x j) (hDb x j) (norm_nonneg _) hC
  algebraMap_mem' c := ⟨fun _ => measurable_const, ‖c‖, norm_nonneg c, fun _ _ => le_rfl⟩
  star_mem' := by
    rintro a ⟨ha,C,hC,hCa⟩
    refine ⟨fun j => continuous_star.measurable.comp (ha j), C,hC, fun x j => ?_⟩
    simpa using hCa x j
abbrev DiagonalSymbol := ↥diagonalSymbols
namespace DiagonalSymbol
instance : CoeFun DiagonalSymbol (fun _ => Base → ℤ → ℂ) := ⟨fun a => a.val⟩
noncomputable def bound (a : DiagonalSymbol) : ℝ := a.property.2.choose
lemma bound_nonneg (a : DiagonalSymbol) : 0 ≤ a.bound := a.property.2.choose_spec.1
lemma norm_le_bound (a : DiagonalSymbol) (x : Base) (j : ℤ) : ‖a x j‖ ≤ a.bound :=
  a.property.2.choose_spec.2 x j
@[simp] lemma zero_apply (x : Base) (j : ℤ) : (0 : DiagonalSymbol) x j = 0 := rfl
@[simp] lemma one_apply (x : Base) (j : ℤ) : (1 : DiagonalSymbol) x j = 1 := rfl
@[simp] lemma add_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a+b) x j = a x j + b x j := rfl
@[simp] lemma mul_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a*b) x j = a x j * b x j := rfl
@[simp] lemma sub_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a-b) x j = a x j - b x j := rfl
@[simp] lemma star_apply (a : DiagonalSymbol) (x : Base) (j : ℤ) : (star a) x j = star (a x j) := rfl
@[simp] lemma smul_apply (c : ℂ) (a : DiagonalSymbol) (x : Base) (j : ℤ) : (c • a) x j = c * a x j := rfl
@[simp] lemma algebraMap_apply (c : ℂ) (x : Base) (j : ℤ) :
    algebraMap ℂ DiagonalSymbol c x j = c := rfl
@[simp] lemma pow_apply (a : DiagonalSymbol) (n : ℕ) (x : Base) (j : ℤ) :
    (a^n) x j = (a x j)^n := by induction n <;> simp_all [pow_succ]
end DiagonalSymbol

def diagonalFiber (a : DiagonalSymbol) (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberMultiplier (a x) a.bound a.bound_nonneg (a.norm_le_bound x)
@[simp] lemma diagonalFiber_apply (a : DiagonalSymbol) (x : Base) (v : Fiber) (j : ℤ) :
    diagonalFiber a x v j = a x j*v j := rfl
end
end BackwardIntertwiners

end OAI


