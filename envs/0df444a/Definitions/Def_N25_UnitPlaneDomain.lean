-- Prove2me | Definitions.Def_N25_UnitPlaneDomain
-- name    : N25_UnitPlaneDomain
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:55.646205+00:00
-- url     : https://prove2.me/theorems/fc4231ac-405e-4f50-a2ef-a64e105d842e
-- title:
--   Domain properties of the modular-unit plane model
-- statement:
--   Packages the monicity and degree-$4$ presentation of the plane relation $F(u,v)$ in $v$, the irreducibility of its specialization $v^4-v^3-2v^2-4v+1$, and the resulting domain structure of $A=ℚ[u,v]/(F)$. It also records that $u$, $v$, and the common birational denominator are nonzero and that the associated principal-open localization is a domain, providing the fraction-field foundation for the modular-unit model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneRing
/-! Irreducibility of the plane relation by monic specialization and reduction modulo two. -/
namespace N25
open Polynomial

private theorem quartic_monic {k : Type*} [CommRing k] [Nontrivial k] :
    (X^4-X^3-2*X^2-4*X+1 : Polynomial k).Monic := by
  have h : degree (-X^3-2*X^2-4*X+1 : Polynomial k) < 4 := by
    compute_degree <;> norm_num
  convert monic_X_pow_add h using 1 <;> ring

private theorem binary_quartic_irreducible :
    Irreducible (X^4+X^3+1 : Polynomial (ZMod 2)) := by
  have hcy : cyclotomic 15 (ZMod 2) = (X^4+X^3+1)*(X^4+X+1) := by
    rw [cyclotomic_eq_X_pow_sub_one_div (by decide : 0 < 15)]
    have hd : Nat.properDivisors 15 = {1,3,5} := by decide
    rw [hd]
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    norm_num [cyclotomic_prime, Finset.sum_range_succ]
    have hm2 : (1+X+X^2 : Polynomial (ZMod 2)).Monic := by
      have h : degree (X+1 : Polynomial (ZMod 2)) < 2 := by compute_degree <;> norm_num
      convert monic_X_pow_add h using 1 <;> ring
    have hm4 : (1+X+X^2+X^3+X^4 : Polynomial (ZMod 2)).Monic := by
      have h : degree (X^3+X^2+X+1 : Polynomial (ZMod 2)) < 4 := by compute_degree <;> norm_num
      convert monic_X_pow_add h using 1 <;> ring
    have hm := ((monic_X_sub_C (1 : ZMod 2)).mul hm2).mul hm4
    have he : (X^15-1 : Polynomial (ZMod 2)) =
        ((X-1)*((1+X+X^2)*(1+X+X^2+X^3+X^4)))*((X^4+X^3+1)*(X^4+X+1)) := by
      have h2 : (2 : Polynomial (ZMod 2)) = 0 := by exact CharP.cast_eq_zero (Polynomial (ZMod 2)) 2
      have h4 : (4 : Polynomial (ZMod 2)) = 0 := by
        calc (4 : Polynomial (ZMod 2)) = 2+2 := by norm_num
             _ = 0 := by rw [h2]; simp
      ring_nf
      simp [h2,h4]
    rw [he]
    apply mul_divByMonic_cancel_left
    simpa only [map_one, mul_assoc] using hm
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (n := 15) (by decide)
  · rw [hcy]; exact dvd_mul_right _ _
  · have ho : orderOf (ZMod.unitOfCoprime 2 (show Nat.Coprime 2 15 by decide)) = 4 := by
      apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
      constructor
      · decide
      · intro m hm hm0
        interval_cases m <;> decide
    rw [ho]
    compute_degree <;> norm_num

private theorem rational_quartic_irreducible :
    Irreducible (X^4-X^3-2*X^2-4*X+1 : Polynomial ℚ) := by
  have hm := quartic_monic (k := ℤ)
  have hi : Irreducible (X^4-X^3-2*X^2-4*X+1 : Polynomial ℤ) := by
    apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ hm
    have h2 : (2 : Polynomial (ZMod 2)) = 0 := by exact CharP.cast_eq_zero (Polynomial (ZMod 2)) 2
    have h4 : (4 : Polynomial (ZMod 2)) = 0 := by
        calc (4 : Polynomial (ZMod 2)) = 2+2 := by norm_num
             _ = 0 := by rw [h2]; simp
    have hn : ∀ p : Polynomial (ZMod 2), -p = p := by
      intro p
      have h : (2 : Polynomial (ZMod 2))*p = 0 := by rw [h2,zero_mul]
      linear_combination -h
    simpa [h2,h4,hn,sub_eq_add_neg] using binary_quartic_irreducible
  have hr := (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hi
  simpa using hr

/-- The relation is monic in its second coordinate. -/
theorem unitPlanePolynomial_monic : unitPlanePolynomial.Monic := by
  let u : Polynomial ℚ := X
  have h : degree (-(C (u^3) : Polynomial (Polynomial ℚ))*X^3 + C (u-u^3-2*u^4)*X^2 -
      C (u^3+u^4+2*u^5)*X + C (u^7)) < 4 := by
    compute_degree <;> norm_num
  convert monic_X_pow_add h using 1
  unfold unitPlanePolynomial planeRelation
  dsimp [u]
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring

/-- Specialization u=1 is an irreducible rational quartic, so the monic plane relation is irreducible. -/
theorem unitPlanePolynomial_irreducible : Irreducible unitPlanePolynomial := by
  apply Monic.irreducible_of_irreducible_map (evalRingHom 1) _ unitPlanePolynomial_monic
  convert rational_quartic_irreducible using 1
  simp [unitPlanePolynomial, planeRelation]
  ring

/-- The coordinate ring of the plane relation is a domain. -/
theorem unitPlaneRing_isDomain : IsDomain UnitPlaneRing :=
  AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp unitPlanePolynomial_irreducible)

/-- The rational quartic obtained by specializing the first plane coordinate to one is irreducible. -/
theorem unitPlaneSpecializedQuartic_irreducible :
    Irreducible (Polynomial.X^4-Polynomial.X^3-2*Polynomial.X^2-4*Polynomial.X+1 : Polynomial ℚ) :=
  rational_quartic_irreducible

/-- The plane relation has exactly degree four in v. -/
theorem unitPlanePolynomial_degree : unitPlanePolynomial.degree = 4 := by
  unfold unitPlanePolynomial planeRelation
  compute_degree <;> norm_num

/-- The first coordinate is nonzero in the plane coordinate ring. -/
theorem unitPlaneU_ne_zero : unitPlaneU ≠ 0 := by
  change AdjoinRoot.mk unitPlanePolynomial (C X) ≠ 0
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial_monic
  · exact C_ne_zero.mpr X_ne_zero
  · rw [unitPlanePolynomial_degree]
    simp

/-- The second coordinate is nonzero in the plane coordinate ring. -/
theorem unitPlaneV_ne_zero : unitPlaneV ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial_monic X_ne_zero
  rw [unitPlanePolynomial_degree]
  simp

/-- The common denominator is nonzero: its representative has v-degree one. -/
theorem unitPlaneDenominator_ne_zero : planeDenominator unitPlaneU unitPlaneV ≠ 0 := by
  have he : planeDenominator unitPlaneU unitPlaneV =
      AdjoinRoot.mk unitPlanePolynomial (X + C ((X : Polynomial ℚ)^2+X)) := by
    change (AdjoinRoot.mk unitPlanePolynomial (C X))^2 +
      AdjoinRoot.mk unitPlanePolynomial (C X) + AdjoinRoot.mk unitPlanePolynomial X = _
    simp only [map_add,map_pow]
    ring
  rw [he]
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial_monic
  · exact (monic_X_add_C _).ne_zero
  · rw [unitPlanePolynomial_degree]
    compute_degree <;> norm_num

/-- Localizing at the denominator does not annihilate the plane coordinate ring. -/
theorem unitPlaneOpenElement_ne_zero : unitPlaneOpenElement ≠ 0 := by
  letI := unitPlaneRing_isDomain
  exact mul_ne_zero (mul_ne_zero unitPlaneU_ne_zero unitPlaneV_ne_zero)
    unitPlaneDenominator_ne_zero

/-- Every power of the open denominator is a non-zero-divisor. -/
theorem unitPlaneOpenPowers_le_nonZeroDivisors :
    Submonoid.powers unitPlaneOpenElement ≤ nonZeroDivisors UnitPlaneRing := by
  letI := unitPlaneRing_isDomain
  intro a ha
  obtain ⟨n,rfl⟩ := ha
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n unitPlaneOpenElement_ne_zero)

/-- The principal open is a domain, because all powers of its denominator are nonzero. -/
theorem unitPlaneOpenRing_isDomain : IsDomain UnitPlaneOpenRing := by
  letI := unitPlaneRing_isDomain
  exact IsLocalization.isDomain_of_le_nonZeroDivisors UnitPlaneOpenRing
    unitPlaneOpenPowers_le_nonZeroDivisors

end N25


