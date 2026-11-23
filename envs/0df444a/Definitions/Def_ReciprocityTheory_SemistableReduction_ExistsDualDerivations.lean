-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
-- name    : ReciprocityTheory_SemistableReduction_ExistsDualDerivations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:32.154789+00:00
-- url     : https://prove2.me/theorems/be22f902-b8ba-4222-b5c3-e030a062e49f
-- title:
--   Exists Dual Derivations
-- statement:
--   Definitions and structural lemmas for Exists Dual Derivations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsDualDerivations.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
namespace DerivationAlgebraicIndependence
open MvPolynomial
section CoeffDer
variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]
noncomputable def coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) : MvPolynomial σ Ω :=
  ∑ n ∈ P.support, monomial n (δ (coeff n P))
theorem coeff_coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) (n : σ →₀ ℕ) :
    coeff n (coeffMap δ P) = δ (coeff n P) := by
  classical
  unfold coeffMap
  rw [coeff_sum]
  by_cases h : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · rw [coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hn
      exact absurd h hn
  · have h0 : coeff n P = 0 := by
      by_contra hc
      exact h (mem_support_iff.mpr hc)
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact h hb
theorem coeffMap_monomial (δ : Derivation K Ω Ω) (n : σ →₀ ℕ) (a : Ω) :
    coeffMap δ (monomial n a) = monomial n (δ a) := by
  classical
  ext m
  rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp
theorem coeffMap_add (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P + Q) = coeffMap δ P + coeffMap δ Q := by
  ext m
  simp only [coeff_add, coeff_coeffMap, map_add]
theorem coeffMap_smul (δ : Derivation K Ω Ω) (k : K) (P : MvPolynomial σ Ω) :
    coeffMap δ (k • P) = k • coeffMap δ P := by
  ext m
  rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_coeffMap,
    Derivation.map_smul]
theorem coeffMap_mul (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P * Q) = P * coeffMap δ Q + Q * coeffMap δ P := by
  induction P using MvPolynomial.induction_on'
  · rename_i u a
    induction Q using MvPolynomial.induction_on'
    · rename_i v b
      rw [monomial_mul, coeffMap_monomial, coeffMap_monomial,
        coeffMap_monomial, monomial_mul, monomial_mul, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, map_add, add_comm v u]
    · rename_i p q hp hq
      simp only [mul_add, add_mul, coeffMap_add, hp, hq]
      ring
  · rename_i p q hp hq
    simp only [add_mul, mul_add, coeffMap_add, hp, hq]
    ring
noncomputable def coeffDer (δ : Derivation K Ω Ω) :
    Derivation K (MvPolynomial σ Ω) (MvPolynomial σ Ω) :=
  Derivation.mk' { toFun := coeffMap δ, map_add' := coeffMap_add δ, map_smul' := coeffMap_smul δ }
    (fun P Q => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; exact coeffMap_mul δ P Q)
end CoeffDer
noncomputable def yPoly {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) (b : Fin D) :
    MvPolynomial (SVars D m) Ω :=
  -∑ k, X (Sum.inr (b.succ, k)) * C (x k)
noncomputable def gFam {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) :
    SVars D m ⊕ Fin D → MvPolynomial (SVars D m) Ω :=
  Sum.elim X (yPoly x)
def eIdx (D m : ℕ) (p : Fin (D + 1) × Fin (m + 1)) : SVars D m ⊕ Fin D :=
  Fin.cases (motive := fun _ => SVars D m ⊕ Fin D)
    (Fin.cases (motive := fun _ => SVars D m ⊕ Fin D) (Sum.inl (Sum.inl ())) Sum.inr p.1)
    (fun j => Sum.inl (Sum.inr (p.1, j))) p.2
end DerivationAlgebraicIndependence
end ReciprocityTheory.MultiplicativeHeights


