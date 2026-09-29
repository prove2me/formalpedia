-- Prove2me | Definitions.Def_ModularCurve_LambdaNodeLocalized
-- name    : ModularCurve_LambdaNodeLocalized
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f5b09516-64e0-515d-b950-61ba1bee3b85
-- title:
--   Local ring of the λ-model at a closed point
-- statement:
--   Fix a level $N\ge 1$, a commutative ring $L$ with a subring $A$, a field $k$ and a ring homomorphism $\mathrm{red}\colon A\to k$, together with two elements $a,b\in k$.
--
--   The first declaration, `lambdaEval`, is the ring homomorphism $A[X_0,X_1]\to L((q))$ (from `MvPolynomial (Fin 2) A` to `LaurentSeries L`) which sends a coefficient $\alpha\in A$ to the corresponding constant Laurent series (the map `CharPReduction.constSeries A`, i.e. the inclusion $A\subseteq L$ followed by $L\to L((q))$), and sends $X_0,X_1$ to `lambdaModC L` and `lambdaNModC L N` respectively. Here `lambdaModC L` is the image in $L((q))$, under coefficientwise reduction along $\mathbb Z\to L$, of the integral Laurent series `lambdaInt`, namely $q$ times the product of the eighth power of the eta product $\prod_{n\ge 1}(1-q^{n})$, the sixteenth power of that product with $q$ replaced by $q^{4}$, and the inverse of its twenty-fourth power with $q$ replaced by $q^{2}$; and `lambdaNModC L N` is obtained from `lambdaModC L` by the substitution $q\mapsto q^{N}$.
--
--   The second declaration, `lambdaLocalizedAtPoint`, is the subring of $L((q))$ whose elements are those $f$ for which there exist $r,s\in A[X_0,X_1]$ with $\mathrm{red}$-reduced value $s(a,b)\ne 0$ in $k$ (the homomorphism `NodeLocalized.pointEval`, which reduces coefficients by $\mathrm{red}$ and evaluates at $(a,b)$) and $f\cdot s(\lambda,\lambda_N)=r(\lambda,\lambda_N)$, where $\lambda,\lambda_N$ denote the two series above. Thus membership is the existence of a fractional presentation with denominator not vanishing at the chosen point of the special fibre; no nonvanishing of $s(\lambda,\lambda_N)$ itself is demanded, and no uniqueness of $(r,s)$ is asserted. Two further lemmas record the membership criterion as a restatement of the definition and the fact that every value of `lambdaEval` lies in this subring.
--
--   **Relation to Mathlib.** Mathlib has no notion of this kind; the subring is the project's own, a concrete realisation inside Laurent series of a localisation at a point. It is a variant of `NodeLocalized.modularLocalizedAtPoint`, with the pair of generators $j(q), j(q^N)$ replaced by the $\lambda$-series $\lambda(q), \lambda(q^N)$, and it reuses the generator-free evaluation map `NodeLocalized.pointEval`.
--
--   **Where it is used.** These rings serve the analysis of the reduction of a two-variable plane model of a modular curve, generated here by $\lambda(q)$ and $\lambda(q^N)$ rather than by $j$-series, at a closed point $(a,b)$ of its special fibre. They are the local rings whose properties at such points feed the characteristic-$p$ geometry used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LambdaNodeLocalized.lean

import Mathlib
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_LambdaSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace LambdaNodeLocalized

open CharPReduction

section Point

variable (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def lambdaEval : MvPolynomial (Fin 2) A →+* LaurentSeries L :=
  MvPolynomial.eval₂Hom (CharPReduction.constSeries A) ![lambdaModC L, lambdaNModC L N]

def lambdaLocalizedAtPoint : Subring (LaurentSeries L) where
  carrier := {f | ∃ r s : MvPolynomial (Fin 2) A,
    NodeLocalized.pointEval A red a b s ≠ 0 ∧ f * lambdaEval N A s = lambdaEval N A r}
  zero_mem' := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, map_zero, zero_mul]⟩
  one_mem' := ⟨1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * t + u * s, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (lambdaEval N A s * lambdaEval N A t)
        = f * lambdaEval N A s * lambdaEval N A t + g * lambdaEval N A t * lambdaEval N A s := by ring
      _ = lambdaEval N A r * lambdaEval N A t + lambdaEval N A u * lambdaEval N A s := by rw [hf, hg]
  neg_mem' := by
    rintro f ⟨r, s, hs, hf⟩
    exact ⟨-r, s, hs, by rw [neg_mul, hf, map_neg]⟩
  mul_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * u, s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, map_mul]
    calc f * g * (lambdaEval N A s * lambdaEval N A t)
        = (f * lambdaEval N A s) * (g * lambdaEval N A t) := by ring
      _ = lambdaEval N A r * lambdaEval N A u := by rw [hf, hg]

theorem mem_lambdaLocalizedAtPoint {f : LaurentSeries L} :
    f ∈ lambdaLocalizedAtPoint N A red a b ↔
      ∃ r s : MvPolynomial (Fin 2) A,
        NodeLocalized.pointEval A red a b s ≠ 0 ∧ f * lambdaEval N A s = lambdaEval N A r :=
  Iff.rfl

theorem lambdaEval_mem_lambdaLocalizedAtPoint (p : MvPolynomial (Fin 2) A) :
    lambdaEval N A p ∈ lambdaLocalizedAtPoint N A red a b :=
  ⟨p, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩

end Point

end LambdaNodeLocalized
end ModularCurve

end


