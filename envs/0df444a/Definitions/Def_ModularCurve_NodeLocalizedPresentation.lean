-- Prove2me | Definitions.Def_ModularCurve_NodeLocalizedPresentation
-- name    : ModularCurve_NodeLocalizedPresentation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/7eb0e620-3ade-5f78-80cf-830e73c16fa0
-- title:
--   Node ring as a localisation of the modular image ring
-- statement:
--   Throughout, $N$ is a positive level, $L$ a field, $A$ a subring of $L$, $k$ a field and $\mathrm{red} \colon A \to k$ a ring homomorphism, together with a pair $(a,b)$ of elements of $k$. Two homomorphisms out of $S = A[X_0,X_1]$ are in play: `modularEval`, which sends a coefficient $c \in A$ to the constant Laurent series $c$ and $(X_0,X_1)$ to the pair $(\,j(\mathsf q),\ j(\mathsf q^N)\,)$ of $q$-expansions in $L(\!(\mathsf q)\!)$; and `pointEval`, which applies $\mathrm{red}$ to coefficients and sends $(X_0,X_1) \mapsto (a,b)$. The node ring `modularLocalizedAtPoint` consists of those $f \in L(\!(\mathsf q)\!)$ admitting $r,s \in S$ with $\mathrm{pointEval}(s) \neq 0$ and $f \cdot \mathrm{modularEval}(s) = \mathrm{modularEval}(r)$.
--
--   Defined here are: `modularEvalAt`, the corestriction of `modularEval` to that subring; `evalRange`, the image subring $A[j,j_N]$ of `modularEval`, which is contained in the node ring and hence makes the node ring an `evalRange`-algebra by inclusion; and `nodeDenominators`, the submonoid of `evalRange` of elements $\mathrm{modularEval}(s)$ with $\mathrm{pointEval}(s) \neq 0$, with membership criteria.
--
--   Under the standing hypothesis that $\ker(\mathrm{modularEval}) \subseteq \ker(\mathrm{pointEval})$, such denominators have nonzero image, their images in the node ring are units, the node ring is exhibited as the localisation of `evalRange` at `nodeDenominators`, and it is a local ring.
--
--   Two further results are independent of that hypothesis: for any commutative ring $R$ and $v \colon \mathrm{Fin}\,2 \to R$, $p - C(p(v))$ lies in the ideal $(X_0 - C v_0,\, X_1 - C v_1)$; and if $\mathrm{red}(x)=a$, $\mathrm{red}(y)=b$ and $\ker(\mathrm{red}) = \varpi A$, then $\ker(\mathrm{pointEval}) = (C\varpi,\ X_0 - Cx,\ X_1 - Cy)$.
--
--   **Relation to Mathlib.** The localisation and locality assertions are phrased with Mathlib's `IsLocalization` and `IsLocalRing`; the modular image ring, the node ring and the denominator monoid are the project's own constructions inside the Laurent series field, no quotient types being used in place of $S/\ker(\mathrm{modularEval})$.
--
--   **Where it is used.** These presentations make Mathlib's localisation machinery available for the node ring attached to a point of a modular curve in characteristic $p$ — noetherianity, locality, its maximal ideal and dimension, and primality of the branch ideals — which feed the local study of the reduction of $X_0$ at the relevant prime used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_NodeLocalizedPresentation.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

def modularEvalAt : MvPolynomial (Fin 2) A →+* modularLocalizedAtPoint N A red a b :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularLocalizedAtPoint N A red a b)

@[simp] theorem coe_modularEvalAt (p : MvPolynomial (Fin 2) A) :
    (modularEvalAt N A red a b p : LaurentSeries L) = modularEval N A p := rfl

abbrev evalRange : Subring (LaurentSeries L) := (modularEval N A).range

theorem evalRange_le : evalRange N A ≤ modularLocalizedAtPoint N A red a b := by
  rintro _ ⟨p, rfl⟩
  exact modularEval_mem_modularLocalizedAtPoint N A red a b p

instance algebraEvalRange : Algebra (evalRange N A) (modularLocalizedAtPoint N A red a b) :=
  (Subring.inclusion (evalRange_le N A red a b)).toAlgebra

theorem algebraMap_evalRange_coe (y : evalRange N A) :
    ((algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) y : modularLocalizedAtPoint N A red a b) :
      LaurentSeries L) = y := rfl

theorem algebraMap_evalRange_rangeRestrict (p : MvPolynomial (Fin 2) A) :
    algebraMap (evalRange N A) (modularLocalizedAtPoint N A red a b) ((modularEval N A).rangeRestrict p)
      = modularEvalAt N A red a b p := rfl

def nodeDenominators : Submonoid (evalRange N A) where
  carrier := {y | ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ (modularEval N A).rangeRestrict s = y}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]⟩
  mul_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, by rw [map_mul]⟩

theorem rangeRestrict_mem_nodeDenominators {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    (modularEval N A).rangeRestrict s ∈ nodeDenominators N A red a b :=
  ⟨s, hs, rfl⟩

theorem mem_nodeDenominators_iff (y : evalRange N A) :
    y ∈ nodeDenominators N A red a b ↔ ∃ s : MvPolynomial (Fin 2) A, pointEval A red a b s ≠ 0 ∧ modularEval N A s = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, Subtype.ext h⟩

section KerLE

variable [hker : Fact (RingHom.ker (modularEval N A) ≤ RingHom.ker (pointEval A red a b))]

theorem modularEval_ne_zero_of_pointEval_ne_zero {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    modularEval N A s ≠ 0 := fun h => hs (hker.out ((RingHom.mem_ker).mpr h))

theorem isUnit_modularEvalAt {s : MvPolynomial (Fin 2) A} (hs : pointEval A red a b s ≠ 0) :
    IsUnit (modularEvalAt N A red a b s) := by
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  refine isUnit_iff_exists_inv.mpr ⟨⟨(modularEval N A s)⁻¹, 1, s, hs, ?_⟩, Subtype.ext ?_⟩
  · rw [map_one, inv_mul_cancel₀ hs0]
  · exact mul_inv_cancel₀ hs0

instance isLocalization_nodeDenominators :
    IsLocalization (nodeDenominators N A red a b) (modularLocalizedAtPoint N A red a b) where
  map_units := by
    rintro ⟨_, s, hs, rfl⟩
    rw [algebraMap_evalRange_rangeRestrict]
    exact isUnit_modularEvalAt N A red a b hs
  surj := fun z => by
    obtain ⟨r, s, hs, h⟩ := z.2
    exact ⟨⟨(modularEval N A).rangeRestrict r, ⟨(modularEval N A).rangeRestrict s,
      rangeRestrict_mem_nodeDenominators N A red a b hs⟩⟩, Subtype.ext h⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext (congrArg (fun w : modularLocalizedAtPoint N A red a b => (w : LaurentSeries L)) h)⟩

instance isLocalRing_modularLocalizedAtPoint : IsLocalRing (modularLocalizedAtPoint N A red a b) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨r, s, hs, h⟩ := z.2
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  have hz : (z : LaurentSeries L) = modularEval N A r * (modularEval N A s)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  by_cases hr : pointEval A red a b r = 0
  · right
    have hsr : pointEval A red a b (s - r) ≠ 0 := by rw [map_sub, hr, sub_zero]; exact hs
    have hsr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hsr
    have hsr0' : modularEval N A s - modularEval N A r ≠ 0 := by rwa [map_sub] at hsr0
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A (s - r))⁻¹, s, s - r, hsr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hsr0, mul_one]
    · show (1 - (z : LaurentSeries L)) * (modularEval N A s * (modularEval N A (s - r))⁻¹) = 1
      rw [hz, map_sub]
      field_simp
  · left
    have hr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hr
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A r)⁻¹, s, r, hr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    · show (z : LaurentSeries L) * (modularEval N A s * (modularEval N A r)⁻¹) = 1
      rw [hz]
      field_simp

end KerLE

theorem sub_C_eval_mem_span {R : Type*} [CommRing R] (v : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    p - C (eval v p) ∈ Ideal.span {(X 0 - C (v 0) : MvPolynomial (Fin 2) R), X 1 - C (v 1)} := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [eval_C, sub_self]; exact zero_mem _
  | add p r hp hr =>
    have : p + r - C (eval v (p + r)) = (p - C (eval v p)) + (r - C (eval v r)) := by rw [map_add, map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p i hp =>
    have : p * X i - C (eval v (p * X i)) = (p - C (eval v p)) * X i + C (eval v p) * (X i - C (v i)) := by
      rw [map_mul, eval_X, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem ker_pointEval_eq_span (x y : A) (hx : red x = a) (hy : red y = b) (ϖ : A)
    (hϖ : ∀ c : A, red c = 0 ↔ ∃ d, c = ϖ * d) :
    RingHom.ker (pointEval A red a b) = Ideal.span {C ϖ, X 0 - C x, X 1 - C y} := by
  have hpe : ∀ p : MvPolynomial (Fin 2) A, pointEval A red a b p = red (eval ![x, y] p) := by
    intro p
    have hfun : (![a, b] : Fin 2 → k) = red ∘ ![x, y] := by
      funext i; fin_cases i <;> simp [hx, hy]
    rw [pointEval, coe_eval₂Hom, hfun, eval, coe_eval₂Hom, eval₂_comp_left, RingHom.comp_id]
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker, hpe] at hp
    obtain ⟨d, hd⟩ := (hϖ _).mp hp
    have : p = (p - C (eval ![x, y] p)) + C ϖ * C d := by rw [hd, map_mul]; ring
    rw [this]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    exact Ideal.span_mono (Set.subset_insert _ _) (sub_C_eval_mem_span ![x, y] p)
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, RingHom.mem_ker, hpe]
    · rw [eval_C]; exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
    · simp
    · simp

end Presentation

end NodeLocalized
end ModularCurve

end


