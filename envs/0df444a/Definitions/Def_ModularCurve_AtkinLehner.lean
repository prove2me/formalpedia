-- Prove2me | Definitions.Def_ModularCurve_AtkinLehner
-- name    : ModularCurve_AtkinLehner
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/7b7a4e1c-636d-5264-8d4e-84450502362a
-- title:
--   Fricke involution and the cusps 0 and ∞ on X0​(N)
-- statement:
--   Fix $N$ with `[NeZero N]`. Throughout, `modularFunctionField N`, `modularFunctionFieldFull N`, `modularFunctionFieldBar N`, the elements `jq`, `jqN N`, the operator `qExpand`, the coefficient embedding `coeffEmb`, the places `cuspInfty N`, `cuspInftyFull N`, `qInftyPlaceBar`, `qIntegersBar`, the subalgebra `laurentBaseChange` and the type `Place` are the project's own notions, defined in the imported modules.
--
--   On the two-generator model, `IsFrickeAut N σ` is a predicate on a $\mathbb{Q}$-algebra automorphism $\sigma$ of `modularFunctionField N`: it asserts exactly the two equations $\sigma(jq) = jqN\,N$ and $\sigma(jqN\,N) = jq$, i.e. that $\sigma$ exchanges the two distinguished generators (classically $j(q)\leftrightarrow j(q^N)$, the effect of $\tau\mapsto -1/(N\tau)$); the generators are written as the subtype literals $\langle jq, jq\_mem\,N\rangle$, $\langle jqN\,N, jqN\_mem\,N\rangle$. `frickeInvolution N` is then a total, closed term: a classically chosen automorphism satisfying `IsFrickeAut N` if one exists, and `AlgEquiv.refl` otherwise. The two normal forms `isFrickeAut_frickeInvolution` and `frickeInvolution_eq_refl` record precisely these two cases, each taking only the (non-)existence hypothesis; no existence, uniqueness or involutivity is asserted here. `cuspZero N` is defined as the translate `frickeInvolution N • cuspInfty N` of the place at $q=0$ under the action of field automorphisms on places, with `cuspZero_def` the definitional unfolding.
--
--   The `Full` section repeats this on the all-divisors model: `IsFrickeAutFull N σ` says that for every factorisation $a\cdot b = N$ with $a,b$ nonzero, $\sigma$ sends `qExpand ℚ a jq` to `qExpand ℚ b jq` (the product form, avoiding natural-number division), and `frickeInvolutionFull N`, its two normal forms and `cuspZeroFull N := frickeInvolutionFull N • cuspInftyFull N` are the exact analogues; the two choices are made independently.
--
--   Finally, `order_coeffEmb_jq` computes that the Hahn-series order of `coeffEmb L jq` is $-1$ for any field $L$ over $\mathbb{Q}$ (from $q^{-1}$ having coefficient $1$), and `cuspInftyBar N` uses this to instantiate `qInftyPlaceBar` at `coeffEmb (AlgebraicClosure ℚ) jq`, giving a place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$; `cuspInftyBar_toValuationSubring` states that its valuation subring is `qIntegersBar`, by `rfl`.
--
--   **Relation to Mathlib.** Mathlib has no modular function fields, no Atkin–Lehner or Fricke involutions and no places of curves; all of those are the project's own. Only general Mathlib machinery is used here: $\mathbb{Q}$-algebra equivalences (`AlgEquiv`), classical choice, and the order of a Hahn series.
--
--   **Where it is used.** These definitions fix the meaning of the Fricke involution and of the cusp $0$ on both $\mathbb{Q}$-models of the function field of $X_0(N)$, and of the cusp $\infty$ over $\overline{\mathbb{Q}}$ on the field carrying the project's $J_0(N)$ data. They are the base for the statements about $J_0(N)$ — its cusps, reduction at primes $\ell \nmid Np$ and the Eichler–Shimura relation — which feed the modularity and level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AtkinLehner.lean

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Fricke

variable (N : ℕ) [NeZero N]

def IsFrickeAut (σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N) : Prop :=
  σ ⟨jq, jq_mem N⟩ = ⟨jqN N, jqN_mem N⟩ ∧ σ ⟨jqN N, jqN_mem N⟩ = ⟨jq, jq_mem N⟩

open Classical in

def frickeInvolution : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N :=
  if h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ
  then h.choose else AlgEquiv.refl

theorem isFrickeAut_frickeInvolution
    (h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    IsFrickeAut N (frickeInvolution N) := by
  rw [frickeInvolution, dif_pos h]
  exact h.choose_spec

theorem frickeInvolution_eq_refl
    (h : ¬ ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ) :
    frickeInvolution N = AlgEquiv.refl := by
  rw [frickeInvolution, dif_neg h]

def cuspZero : Place ℚ (modularFunctionField N) := frickeInvolution N • cuspInfty N

theorem cuspZero_def : cuspZero N = frickeInvolution N • cuspInfty N := rfl

end Fricke

section Full

def IsFrickeAutFull (N : ℕ) [NeZero N]
    (σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N) : Prop :=
  ∀ (a b : ℕ) (hab : a * b = N) (_ : NeZero a) (_ : NeZero b),
    σ ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩
      = ⟨qExpand ℚ b jq, jqd_mem_full N (Dvd.intro_left a hab)⟩

open Classical in

def frickeInvolutionFull (N : ℕ) [NeZero N] :
    modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N :=
  if h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ
  then h.choose else AlgEquiv.refl

theorem isFrickeAutFull_frickeInvolutionFull (N : ℕ) [NeZero N]
    (h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    IsFrickeAutFull N (frickeInvolutionFull N) := by
  rw [frickeInvolutionFull, dif_pos h]
  exact h.choose_spec

theorem frickeInvolutionFull_eq_refl (N : ℕ) [NeZero N]
    (h : ¬ ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N,
      IsFrickeAutFull N σ) :
    frickeInvolutionFull N = AlgEquiv.refl := by
  rw [frickeInvolutionFull, dif_neg h]

variable (N : ℕ) [NeZero N]

def cuspZeroFull : Place ℚ (modularFunctionFieldFull N) :=
  frickeInvolutionFull N • cuspInftyFull N

theorem cuspZeroFull_def : cuspZeroFull N = frickeInvolutionFull N • cuspInftyFull N := rfl

end Full

section Bar

theorem order_coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : (coeffEmb L jq).order = -1 := by
  have h1 : (coeffEmb L jq).coeff (-1) ≠ 0 := by
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have h0 : coeffEmb L jq ≠ 0 := fun h => h1 (by rw [h, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0
    (by rw [coeffEmb_coeff, coeff_jq_of_lt h, map_zero])

variable (N : ℕ) [NeZero N]

def cuspInftyBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  qInftyPlaceBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩,
      order_coeffEmb_jq (AlgebraicClosure ℚ)⟩

theorem cuspInftyBar_toValuationSubring :
    (cuspInftyBar N).toValuationSubring
      = qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := rfl

end Bar

end ModularCurve

end


