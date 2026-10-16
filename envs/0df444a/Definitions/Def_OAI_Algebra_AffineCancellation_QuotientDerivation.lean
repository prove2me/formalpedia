-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
-- name    : OAI_Algebra_AffineCancellation_QuotientDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:03:23.325789+00:00
-- url     : https://prove2.me/theorems/d8184be2-34c1-4b3a-be33-e4ec565fa469
-- title:
--   Derivation induced on a quotient ring by a stable ideal
-- statement:
--   Let $k$ be a commutative ring, $R$ a commutative $k$-algebra, $I\subseteq R$ an ideal and $D$ a $k$-linear derivation of $R$ with $D(I)\subseteq I$.
--
--   1. **Induced linear map.** The map $R/I\to R/I$, $r+I\mapsto D(r)+I$, is well defined and $k$-linear because $D$ maps $I$ into $I$.
--
--   2. **Induced derivation.** This map satisfies the Leibniz rule and so defines a $k$-linear derivation $\bar D$ of $R/I$, characterized by
--   $$\bar D(r+I)=D(r)+I\qquad(r\in R).$$
--
--   3. **Principal ideals.** For $h\in R$, if $D(h)\in(h)$ then $D\bigl((h)\bigr)\subseteq(h)$. Hence $D$ descends to $R/(h)$ as soon as $D(h)$ is a multiple of $h$.
--
--   This construction transfers derivations of a polynomial ring to a hypersurface ring $R/(h)$. A typical case is a derivation that kills the defining equation, such as a derivation of $\mathbb{C}[X_0,\dots,X_4]$ that annihilates $X_0X_3-X_2X_1-1$.
--
--   **Formalization Note** The induced linear map `linear I D hD` is obtained with `Submodule.liftQ`, and `derivation I D hD` is built from it with `Derivation.mk'`. Here `hD : ∀ r ∈ I, D r ∈ I`, and the simp lemma `derivation_mk` gives the displayed formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/QuotientDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/QuotientDerivation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading

namespace OAI

noncomputable section

namespace ComplexCancellation.QuotientDerivation
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (I : Ideal R) (D : Derivation k R R)
  (hD : ∀ r ∈ I, D r ∈ I)

def linear : (R ⧸ I) →ₗ[k] (R ⧸ I) :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k I).toLinearMap.comp D.toLinearMap)
    (by intro r hr; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hD r hr))

@[simp] lemma linear_mk (r : R) : linear I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

def derivation : Derivation k (R ⧸ I) (R ⧸ I) := Derivation.mk' (linear I D hD) (by
  intro r s
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  change linear I D hD ((Ideal.Quotient.mk I) r * (Ideal.Quotient.mk I) s) = _
  rw [← map_mul, linear_mk]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, linear_mk])

@[simp] lemma derivation_mk (r : R) : derivation I D hD (Ideal.Quotient.mk I r) =
    Ideal.Quotient.mk I (D r) := rfl

lemma span_singleton_stable {h : R} (hh : D h ∈ Ideal.span {h}) :
    ∀ r ∈ Ideal.span {h}, D r ∈ Ideal.span {h} := by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ hh)

end ComplexCancellation.QuotientDerivation

end

end OAI


