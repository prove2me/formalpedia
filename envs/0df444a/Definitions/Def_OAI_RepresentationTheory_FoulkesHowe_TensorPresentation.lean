-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
-- name    : OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:20:29.336472+00:00
-- url     : https://prove2.me/theorems/42668731-673c-4f17-9e20-91101f0f6fb3
-- title:
--   The multiplication map from the tensor power $V^{\otimes n}$ onto $\mathrm{Sym}^n V$
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$ with canonical map $\iota:V\to S(V)$, and $n\in\mathbb{N}$. Let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of the products $[v_0,\dots,v_{n-1}]=\iota(v_0)\cdots\iota(v_{n-1})$ with $v_i\in V$, and let $V^{\otimes n}$ be the $n$-fold tensor power of $V$ over $\mathbb{C}$, with factors indexed by $\{0,\dots,n-1\}$ (for $n=0$ it is $\mathbb{C}$).
--
--   1. **Product as a multilinear map.** $(v_0,\dots,v_{n-1})\mapsto\iota(v_0)\cdots\iota(v_{n-1})$ is a multilinear map $V^n\to S(V)$.
--   2. **Linearization.** The induced linear map $m:V^{\otimes n}\to S(V)$ satisfies $m(v_0\otimes\cdots\otimes v_{n-1})=[v_0,\dots,v_{n-1}]$, and its range is exactly $\mathrm{Sym}^n V$.
--   3. **Surjection onto the symmetric power.** Restricting the codomain gives a surjective linear map
--   $$m_n:V^{\otimes n}\twoheadrightarrow\mathrm{Sym}^n V,\qquad m_n(v_0\otimes\cdots\otimes v_{n-1})=[v_0,\dots,v_{n-1}].$$
--
--   This presents $\mathrm{Sym}^n V$ as a quotient of the tensor power $V^{\otimes n}$, so that properties of tensor powers, such as finite-dimensionality, pass to symmetric powers.
--
--   **Formalization Note** The tensor power is Mathlib's `PiTensorProduct` over `Fin n`; the maps are `symMonomialMultilinearRaw`, `tensorToSymPowRaw` (with range lemma `tensorToSymPowRaw_range`) and `tensorToSymPow` (with `tensorToSymPow_surjective`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/TensorPresentation.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/TensorPresentation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

universe u

namespace Problem346

variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- Multiplication of degree-one generators as a multilinear map. -/
def symMonomialMultilinearRaw :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymmetricAlgebra ℂ V) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)

@[simp] theorem symMonomialMultilinearRaw_apply (v : Fin n → V) :
    symMonomialMultilinearRaw n V v = symMonomialRaw n V v := rfl

/-- The tensor-power presentation of the homogeneous symmetric power. -/
def tensorToSymPowRaw :
    (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymmetricAlgebra ℂ V :=
  PiTensorProduct.lift (symMonomialMultilinearRaw n V)

@[simp] theorem tensorToSymPowRaw_tprod (v : Fin n → V) :
    tensorToSymPowRaw n V (PiTensorProduct.tprod ℂ v) = symMonomialRaw n V v :=
  PiTensorProduct.lift.tprod _

theorem tensorToSymPowRaw_range :
    LinearMap.range (tensorToSymPowRaw n V) = symPowSubmodule n V := by
  rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, tensorToSymPowRaw_tprod, symPowSubmodule]

/-- Multiplication of tensors, with codomain restricted to degree `n`. -/
def tensorToSymPow : (⨂[ℂ] _ : Fin n, V) →ₗ[ℂ] SymPow n V :=
  (tensorToSymPowRaw n V).codRestrict (symPowSubmodule n V) (fun x => by
    rw [← tensorToSymPowRaw_range]
    exact LinearMap.mem_range_self _ x)

@[simp] theorem tensorToSymPow_tprod (v : Fin n → V) :
    tensorToSymPow n V (PiTensorProduct.tprod ℂ v) = symMonomial n V v := by
  apply Subtype.ext
  exact tensorToSymPowRaw_tprod n V v

theorem tensorToSymPow_surjective : Function.Surjective (tensorToSymPow n V) := by
  intro x
  have hx : x.val ∈ LinearMap.range (tensorToSymPowRaw n V) := by
    rw [tensorToSymPowRaw_range]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

end Problem346

end

end OAI


