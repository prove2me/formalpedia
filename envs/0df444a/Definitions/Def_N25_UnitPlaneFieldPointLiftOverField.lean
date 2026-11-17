-- Prove2me | Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
-- name    : N25_UnitPlaneFieldPointLiftOverField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:49.459984+00:00
-- url     : https://prove2.me/theorems/b009eddb-2bcf-4cbf-b5f4-d7be487ca4a7
-- title:
--   Universal plane-model domain package and function-field evaluation
-- statement:
--   Packages the coefficient-field facts that the monic quartic $F(u,v)$ is irreducible, that $K[u,v]/(F)$ and its denominator principal open are domains with nonzero coordinates and denominator, and that evaluation is injective when $u$ is transcendental over $K$. It then installs the domain structure and defines the resulting $K$-algebra map from the plane fraction field, providing a characteristic-uniform technical certificate for the function-field construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointOverField
/-! Function-field evaluation of the actual unit-plane model over a coefficient field.

The evaluation map lifts to the fraction field because it is injective, which rests on the irreducibility of the
unit-plane polynomial over every field. Those proofs, and the domain and nonvanishing facts for the plane
coordinate ring and its principal open that later definitions use, are carried in this module so that these
definitions depend on no theorem node. -/


/-! ### Monicity and prime-power factor shapes for the unit-plane relation. -/
noncomputable section
namespace N25
open Polynomial
variable {K : Type*} [Field K]

/-- The second-coordinate presentation is monic over every coefficient field. -/
theorem unitPlanePolynomial25C_monic : (unitPlanePolynomial25C K).Monic := by
  let u : Polynomial K := X
  have h : degree (-(C (u^3) : Polynomial (Polynomial K))*X^3 + C (u-u^3-2*u^4)*X^2 -
      C (u^3+u^4+2*u^5)*X + C (u^7)) < 4 := by
    compute_degree; norm_num
  convert monic_X_pow_add h using 1
  unfold unitPlanePolynomial25C planeRelation
  dsimp [u]
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring

/-- The second-coordinate degree is four in every characteristic. -/
theorem unitPlanePolynomial25C_natDegree : (unitPlanePolynomial25C K).natDegree = 4 := by
  unfold unitPlanePolynomial25C planeRelation
  compute_degree <;> norm_num

/-- A divisor of a power of the coordinate variable is a scalar monomial. -/
theorem eq_scalar_monomial_of_dvd_X_pow {q : Polynomial K} {n : ℕ}
    (hq : q ∣ X^n) :
    ∃ i ≤ n, ∃ c : K, c ≠ 0 ∧ q = C c * X^i := by
  obtain ⟨i, hi, h⟩ := (dvd_prime_pow (prime_X (R := K)) n).mp hq
  obtain ⟨e, he⟩ := h.symm
  obtain ⟨c, hc, hC⟩ := Polynomial.isUnit_iff.mp e.isUnit
  refine ⟨i, hi, c, hc.ne_zero, ?_⟩
  rw [← he, ← hC]
  exact mul_comm _ _

/-- Substitution of a scalar monomial leaves nine explicit monomial terms. -/
theorem planeRelation_scalar_monomial (c : K) (i : ℕ) :
    planeRelation X (C c * X^i) =
      C (c^4)*X^(4*i) - C (c^3)*X^(3+3*i) +
      C (c^2)*X^(1+2*i) - C (c^2)*X^(3+2*i) -
      C (2*c^2)*X^(4+2*i) - C c*X^(3+i) -
      C c*X^(4+i) - C (2*c)*X^(5+i) + X^7 := by
  simp only [planeRelation, map_mul, map_pow, map_ofNat]
  simp only [pow_add, pow_mul]
  ring

/-- No nonzero scalar monomial can be a root of the plane relation. -/
theorem planeRelation_scalar_monomial_ne_zero (c : K) (hc : c ≠ 0) (i : ℕ) :
    planeRelation X (C c * X^i) ≠ 0 := by
  intro h
  rw [planeRelation_scalar_monomial] at h
  have hc2 : c^2 ≠ 0 := pow_ne_zero _ hc
  have hc3 : c^3 ≠ 0 := pow_ne_zero _ hc
  have hc4 : c^4 ≠ 0 := pow_ne_zero _ hc
  rcases lt_or_ge i 4 with hi | hi
  · interval_cases i
    · have hh := congrArg (fun p : Polynomial K => p.coeff 0) h
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_zero] at hh
      norm_num at hh <;> simp_all
    · have hh := congrArg (fun p : Polynomial K => p.coeff 7) h
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_zero] at hh
      norm_num at hh <;> simp_all
    · have hh := congrArg (fun p : Polynomial K => p.coeff 9) h
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_zero] at hh
      norm_num at hh <;> simp_all
    · have hh := congrArg (fun p : Polynomial K => p.coeff 6) h
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_zero] at hh
      norm_num at hh <;> simp_all
  · have hh := congrArg (fun p : Polynomial K => p.coeff (4*i)) h
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_zero] at hh
    have h1 : 4*i ≠ 3+3*i := by omega
    have h2 : 4*i ≠ 1+2*i := by omega
    have h3 : 4*i ≠ 3+2*i := by omega
    have h4 : 4*i ≠ 4+2*i := by omega
    have h5 : 4*i ≠ 3+i := by omega
    have h6 : 4*i ≠ 4+i := by omega
    have h7 : 4*i ≠ 5+i := by omega
    have h8 : 4*i ≠ 7 := by omega
    simp_all

/-- A polynomial root would divide the constant term and hence be a scalar monomial. -/
theorem planeRelation_polynomial_ne_zero (t : Polynomial K) : planeRelation X t ≠ 0 := by
  intro h
  have ht : t ∣ X^7 := by
    refine ⟨-t^3 + X^3*t^2 - (X-X^3-2*X^4)*t + (X^3+X^4+2*X^5), ?_⟩
    unfold planeRelation at h
    linear_combination h
  obtain ⟨i, _, c, hc, he⟩ := eq_scalar_monomial_of_dvd_X_pow ht
  rw [he] at h
  exact planeRelation_scalar_monomial_ne_zero c hc i h

/-- Evaluation in the second variable is substitution into the literal relation. -/
theorem unitPlanePolynomial25C_eval (t : Polynomial K) :
    (unitPlanePolynomial25C K).eval t = planeRelation X t := by
  simp [unitPlanePolynomial25C, planeRelation]

/-- The plane relation has no polynomial root over any coefficient field. -/
theorem unitPlanePolynomial25C_no_root (t : Polynomial K) :
    (unitPlanePolynomial25C K).eval t ≠ 0 := by
  rw [unitPlanePolynomial25C_eval]
  exact planeRelation_polynomial_ne_zero t

/-- No monic degree-one polynomial divides the plane relation. -/
theorem unitPlanePolynomial25C_no_linear_factor (g : Polynomial (Polynomial K))
    (hg : g.Monic) (hd : g.natDegree = 1) : ¬g ∣ unitPlanePolynomial25C K := by
  intro hdiv
  have he := hg.eq_X_add_C hd
  apply unitPlanePolynomial25C_no_root (-g.coeff 0)
  obtain ⟨q, hq⟩ := hdiv
  rw [hq, eval_mul, he]
  simp

/-- A monic divisor of a pure coordinate power is itself a coordinate power. -/
theorem monic_eq_X_pow_of_dvd_X_pow {q : Polynomial K} {n d : ℕ}
    (hq : q.Monic) (hd : q.natDegree = d) (hdiv : q ∣ X^n) : q = X^d := by
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (prime_X (R := K)) n).mp hdiv
  have he := eq_of_monic_of_associated hq (monic_X_pow i) hi
  have hid : i = d := by simpa [he] using hd
  simpa [hid] using he

end N25


/-! Low-coefficient obstruction to quadratic factors of the unit-plane relation. -/
noncomputable section
namespace N25
open Polynomial
variable {K : Type*} [Field K]

/-- The two possible constant-term orders force incompatible third coefficients. -/
theorem unitPlane_quadratic_normalized_impossible
    (a c : Polynomial K) (β δ : K) (hβ : β ≠ 0)
    (ha0 : a.coeff 0 = 0) (hc0 : c.coeff 0 = 0)
    (h3 : a+c = -X^3)
    (h2 : C β*X + C δ*X^6 + a*c = X-X^3-2*X^4)
    (h1 : a*(C δ*X^6) + (C β*X)*c = -(X^3+X^4+2*X^5)) : False := by
  have hc1 : c.coeff 1 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 2) h1
    rw [mul_comm a (C δ*X^6)] at hh
    simp only [mul_assoc, coeff_add, coeff_neg, coeff_sub, coeff_C_mul,
      coeff_X_pow_mul', coeff_X_mul, coeff_X_pow, coeff_zero] at hh
    norm_num at hh
    exact hh.resolve_left hβ
  have ha1 : a.coeff 1 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 1) h3
    simpa [hc1] using hh
  have haX : X^2 ∣ a := X_pow_dvd_iff.mpr (by
    intro n hn
    interval_cases n <;> assumption)
  have hcX : X^2 ∣ c := X_pow_dvd_iff.mpr (by
    intro n hn
    interval_cases n <;> assumption)
  have hacX : X^4 ∣ a*c := by
    convert mul_dvd_mul haX hcX using 1 <;> ring
  have hac3 : (a*c).coeff 3 = 0 := X_pow_dvd_iff.mp hacX 3 (by decide)
  have hh := congrArg (fun p : Polynomial K => p.coeff 3) h2
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_X_pow, hac3] at hh
  norm_num at hh

/-- The linear coefficient forces one monomial constant term to have order one. -/
theorem unitPlane_quadratic_one_order
    (a c : Polynomial K) (β δ : K) (i j : ℕ)
    (ha0 : a.coeff 0 = 0) (hc0 : c.coeff 0 = 0)
    (_hi : 1 ≤ i) (_hj : 1 ≤ j)
    (h2 : C β*X^i + C δ*X^j + a*c = X-X^3-2*X^4) :
    i = 1 ∨ j = 1 := by
  by_contra hn
  have hni : i ≠ 1 := fun h => hn (Or.inl h)
  have hnj : j ≠ 1 := fun h => hn (Or.inr h)
  have hh := congrArg (fun p : Polynomial K => p.coeff 1) h2
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X,
    mul_coeff_one, ha0, hc0] at hh
  simp [Ne.symm hni, Ne.symm hnj] at hh

/-- The coefficient relations of two monic quadratics cannot hold. -/
theorem unitPlane_quadratic_relations_impossible
    (a b c d : Polynomial K)
    (ha0 : a.coeff 0 = 0) (hb0 : b.coeff 0 = 0)
    (hc0 : c.coeff 0 = 0) (hd0 : d.coeff 0 = 0)
    (hbd : b*d = X^7) (h3 : a+c = -X^3)
    (h2 : b+d+a*c = X-X^3-2*X^4)
    (h1 : a*d+b*c = -(X^3+X^4+2*X^5)) : False := by
  obtain ⟨i, _, β, hβ, hb⟩ := eq_scalar_monomial_of_dvd_X_pow
    (show b ∣ X^7 from ⟨d, hbd.symm⟩)
  obtain ⟨j, _, δ, hδ, hd⟩ := eq_scalar_monomial_of_dvd_X_pow
    (show d ∣ X^7 from ⟨b, by simpa [mul_comm] using hbd.symm⟩)
  have hi : 1 ≤ i := by
    by_contra hn
    have hz : i = 0 := by omega
    simpa [hb, hz, hβ] using hb0
  have hj : 1 ≤ j := by
    by_contra hn
    have hz : j = 0 := by omega
    simpa [hd, hz, hδ] using hd0
  have hbdne : b*d ≠ 0 := by rw [hbd]; exact pow_ne_zero _ X_ne_zero
  have hij := congrArg (fun p : Polynomial K => p.natDegree) hbd
  rw [natDegree_mul (left_ne_zero_of_mul hbdne) (right_ne_zero_of_mul hbdne),
    hb, hd, natDegree_C_mul_X_pow i β hβ, natDegree_C_mul_X_pow j δ hδ,
    natDegree_X_pow] at hij
  have horder := unitPlane_quadratic_one_order a c β δ i j ha0 hc0 hi hj
    (by simpa [hb, hd] using h2)
  rcases horder with hi1 | hj1
  · have hj6 : j = 6 := by omega
    apply unitPlane_quadratic_normalized_impossible a c β δ hβ ha0 hc0 h3
    · simpa [hb, hd, hi1, hj6] using h2
    · simpa [hb, hd, hi1, hj6] using h1
  · have hi6 : i = 6 := by omega
    apply unitPlane_quadratic_normalized_impossible c a δ β hδ hc0 ha0
    · simpa [add_comm] using h3
    · have hh : C β*X^6 + C δ*X + a*c = X-X^3-2*X^4 := by
        simpa [hb, hd, hi6, hj1] using h2
      convert hh using 1 <;> ring
    · have hh : a*(C δ*X) + (C β*X^6)*c = -(X^3+X^4+2*X^5) := by
        simpa [hb, hd, hi6, hj1] using h1
      convert hh using 1 <;> ring

end N25


/-! Universal-field irreducibility of the literal monic unit-plane relation. -/
noncomputable section
namespace N25
open Polynomial
variable {K : Type*} [Field K]

/-- The plane relation displayed by its second-coordinate coefficients. -/
theorem unitPlanePolynomial25C_coefficients :
    unitPlanePolynomial25C K =
      X^4 - C (X^3)*X^3 + C (X-X^3-2*X^4)*X^2 -
      C (X^3+X^4+2*X^5)*X + C (X^7) := by
  simp only [unitPlanePolynomial25C, planeRelation, map_add, map_sub, map_mul,
    map_pow, map_ofNat]

/-- A monic quadratic is determined by its two lower coefficients. -/
theorem monic_quadratic_shape {R : Type*} [CommRing R] [Nontrivial R]
    (p : Polynomial R) (hp : p.Monic) (hd : p.natDegree = 2) :
    p = X^2 + C (p.coeff 1)*X + C (p.coeff 0) := by
  have hc : p.coeff 2 = 1 := by simpa [hd] using hp.coeff_natDegree
  have he := p.as_sum_range_C_mul_X_pow
  rw [hd] at he
  simpa [Finset.sum_range_succ, hc, add_comm, add_left_comm] using he

/-- Two monic quadratics cannot multiply to the plane relation. -/
theorem unitPlanePolynomial25C_no_quadratic_factors
    (f g : Polynomial (Polynomial K)) (hf : f.Monic) (hg : g.Monic)
    (hfd : f.natDegree = 2) (hgd : g.natDegree = 2)
    (hfg : f*g = unitPlanePolynomial25C K) : False := by
  let a := f.coeff 1
  let b := f.coeff 0
  let c := g.coeff 1
  let d := g.coeff 0
  have hfshape : f = X^2+C a*X+C b := monic_quadratic_shape f hf hfd
  have hgshape : g = X^2+C c*X+C d := monic_quadratic_shape g hg hgd
  have hmap : f.map (evalRingHom 0) * g.map (evalRingHom 0) = X^4 := by
    rw [← Polynomial.map_mul, hfg]
    simp [unitPlanePolynomial25C, planeRelation]
  have hfm : f.map (evalRingHom 0) = X^2 :=
    monic_eq_X_pow_of_dvd_X_pow (hf.map _) (by rw [hf.natDegree_map]; exact hfd)
      ⟨_, hmap.symm⟩
  have hgm : g.map (evalRingHom 0) = X^2 :=
    monic_eq_X_pow_of_dvd_X_pow (hg.map _) (by rw [hg.natDegree_map]; exact hgd)
      ⟨_, by simpa [mul_comm] using hmap.symm⟩
  have ha0 : a.coeff 0 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 1) hfm
    simpa [a, coeff_zero_eq_eval_zero] using hh
  have hb0 : b.coeff 0 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 0) hfm
    simpa [b, coeff_zero_eq_eval_zero] using hh
  have hc0 : c.coeff 0 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 1) hgm
    simpa [c, coeff_zero_eq_eval_zero] using hh
  have hd0 : d.coeff 0 = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 0) hgm
    simpa [d, coeff_zero_eq_eval_zero] using hh
  have hprod : f*g = X^4 + C (a+c)*X^3 + C (b+d+a*c)*X^2 +
      C (a*d+b*c)*X + C (b*d) := by
    rw [hfshape, hgshape]
    simp only [map_add, map_mul]
    ring
  rw [hprod, unitPlanePolynomial25C_coefficients] at hfg
  have hbd : b*d = X^7 := by
    have hh := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 0) hfg
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X] at hh
    norm_num at hh
    exact hh
  have h3 : a+c = -X^3 := by
    have hh := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 3) hfg
    norm_num only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow,
      coeff_X, mul_one, mul_zero, zero_add, add_zero, zero_sub, sub_zero] at hh
    simpa using hh
  have h2 : b+d+a*c = X-X^3-2*X^4 := by
    have hh := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 2) hfg
    norm_num only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow,
      coeff_X, mul_one, mul_zero, zero_add, add_zero, zero_sub, sub_zero] at hh
    simpa using hh
  have h1 : a*d+b*c = -(X^3+X^4+2*X^5) := by
    have hh := congrArg (fun p : Polynomial (Polynomial K) => p.coeff 1) hfg
    norm_num only [coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow,
      coeff_X, mul_one, mul_zero, zero_add, add_zero, zero_sub, sub_zero] at hh
    simpa using hh
  exact unitPlane_quadratic_relations_impossible a b c d ha0 hb0 hc0 hd0 hbd h3 h2 h1

/-- The unit-plane polynomial is irreducible over every coefficient field. -/
theorem unitPlanePolynomial25C_irreducible : Irreducible (unitPlanePolynomial25C K) := by
  have hm := unitPlanePolynomial25C_monic (K := K)
  apply hm.irreducible_iff_natDegree'.mpr
  constructor
  · intro h
    have hd := unitPlanePolynomial25C_natDegree (K := K)
    rw [h] at hd
    norm_num at hd
  · intro f g hf hg hfg hgd
    rw [unitPlanePolynomial25C_natDegree] at hgd
    norm_num only [Nat.reduceDiv, Finset.mem_Ioc] at hgd
    have hg12 : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
    rcases hg12 with hg1 | hg2
    · exact unitPlanePolynomial25C_no_linear_factor g hg hg1 ⟨f, by rw [mul_comm, hfg]⟩
    · have hdeg := congrArg (fun p : Polynomial (Polynomial K) => p.natDegree) hfg
      rw [hf.natDegree_mul hg, unitPlanePolynomial25C_natDegree, hg2] at hdeg
      have hf2 : f.natDegree = 2 := by omega
      exact unitPlanePolynomial25C_no_quadratic_factors f g hf hg hf2 hg2 hfg

end N25

/-! ### Domain and nonvanishing consequences of universal unit-plane irreducibility -/
noncomputable section
namespace N25
open Polynomial
variable {K : Type*} [Field K]

/-- The plane polynomial has degree four over every coefficient field. -/
theorem unitPlanePolynomial25C_degree : (unitPlanePolynomial25C K).degree = 4 := by
  rw [degree_eq_natDegree unitPlanePolynomial25C_monic.ne_zero,
    unitPlanePolynomial25C_natDegree]
  rfl

/-- The plane coordinate ring is a domain over every coefficient field. -/
theorem unitPlaneRing25C_isDomain : IsDomain (UnitPlaneRing25C K) :=
  AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp unitPlanePolynomial25C_irreducible)

/-- The first coordinate is nonzero in the plane coordinate ring. -/
theorem unitPlaneU25C_ne_zero : (unitPlaneU25C K) ≠ 0 := by
  change AdjoinRoot.mk (unitPlanePolynomial25C K) (C X) ≠ 0
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial25C_monic
  · exact C_ne_zero.mpr X_ne_zero
  · rw [unitPlanePolynomial25C_degree]
    simp

/-- The second coordinate is nonzero in the plane coordinate ring. -/
theorem unitPlaneV25C_ne_zero : (unitPlaneV25C K) ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial25C_monic X_ne_zero
  rw [unitPlanePolynomial25C_degree]
  simp

/-- The common denominator is nonzero: its representative has v-degree one. -/
theorem unitPlaneDenominator25C_ne_zero : planeDenominator (unitPlaneU25C K) (unitPlaneV25C K) ≠ 0 := by
  have he : planeDenominator (unitPlaneU25C K) (unitPlaneV25C K) =
      AdjoinRoot.mk (unitPlanePolynomial25C K) (X + C ((X : Polynomial K)^2+X)) := by
    change (AdjoinRoot.mk (unitPlanePolynomial25C K) (C X))^2 +
      AdjoinRoot.mk (unitPlanePolynomial25C K) (C X) + AdjoinRoot.mk (unitPlanePolynomial25C K) X = _
    simp only [map_add,map_pow]
    ring
  rw [he]
  apply AdjoinRoot.mk_ne_zero_of_degree_lt unitPlanePolynomial25C_monic
  · exact (monic_X_add_C _).ne_zero
  · rw [unitPlanePolynomial25C_degree]
    compute_degree <;> norm_num

/-- Localizing at the denominator does not annihilate the plane coordinate ring. -/
theorem unitPlaneOpenElement25C_ne_zero : (unitPlaneOpenElement25C K) ≠ 0 := by
  letI := unitPlaneRing25C_isDomain (K := K)
  exact mul_ne_zero (mul_ne_zero unitPlaneU25C_ne_zero unitPlaneV25C_ne_zero)
    unitPlaneDenominator25C_ne_zero

/-- Every power of the open denominator is a non-zero-divisor. -/
theorem unitPlaneOpenPowers25C_le_nonZeroDivisors :
    Submonoid.powers (unitPlaneOpenElement25C K) ≤ nonZeroDivisors (UnitPlaneRing25C K) := by
  letI := unitPlaneRing25C_isDomain (K := K)
  intro a ha
  obtain ⟨n,rfl⟩ := ha
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n unitPlaneOpenElement25C_ne_zero)

/-- The principal open is a domain, because all powers of its denominator are nonzero. -/
theorem unitPlaneOpenRing25C_isDomain : IsDomain (UnitPlaneOpenRing25C K) := by
  letI := unitPlaneRing25C_isDomain (K := K)
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (UnitPlaneOpenRing25C K)
    (unitPlaneOpenPowers25C_le_nonZeroDivisors (K := K))

/-- Good-prime specialization of universal-field irreducibility. -/
theorem unitPlanePolynomial25C_irreducible_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    Irreducible (unitPlanePolynomial25C K) := by
  cases hp <;> exact unitPlanePolynomial25C_irreducible

/-- The signed good-prime plane coordinate ring is a domain. -/
theorem unitPlaneRing25C_isDomain_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    IsDomain (UnitPlaneRing25C K) := by
  cases hp <;> exact unitPlaneRing25C_isDomain

/-- The signed good-prime denominator remains nonzero. -/
theorem unitPlaneOpenElement25C_ne_zero_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    unitPlaneOpenElement25C K ≠ 0 := by
  cases hp <;> exact unitPlaneOpenElement25C_ne_zero

end N25


/-! Injectivity of field-valued plane evaluation with transcendental first coordinate. -/
namespace N25

/-- Plane evaluation restricts to polynomial evaluation in the first coordinate. -/
theorem unitPlaneFieldPointEvaluation25C_base
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (a : Polynomial K) :
    unitPlaneFieldPointEvaluation25C (K := K) u v hr
      (algebraMap (Polynomial K) (UnitPlaneRing25C K) a) = Polynomial.aeval u a := by
  simp [unitPlaneFieldPointEvaluation25C, AdjoinRoot.algebraMap_eq]

/-- Transcendence of the first coordinate makes plane evaluation injective. -/
theorem unitPlaneFieldPointEvaluation25C_injective
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u) :
    Function.Injective (unitPlaneFieldPointEvaluation25C (K := K) u v hr) := by
  let : IsDomain (UnitPlaneRing25C K) := unitPlaneRing25C_isDomain
  let : Module.Finite (Polynomial K) (UnitPlaneRing25C K) :=
    unitPlanePolynomial25C_monic.finite_adjoinRoot
  let : Algebra.IsIntegral (Polynomial K) (UnitPlaneRing25C K) :=
    Algebra.IsIntegral.of_finite _ _
  change Function.Injective (unitPlaneFieldPointEvaluation25C (K := K) u v hr).toRingHom
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial K)
  ext a
  change unitPlaneFieldPointEvaluation25C (K := K) u v hr
    (algebraMap (Polynomial K) (UnitPlaneRing25C K) a) = 0 ↔ a = 0
  rw [unitPlaneFieldPointEvaluation25C_base]
  constructor
  · intro ha
    apply (transcendental_iff_injective.mp hu)
    simpa using ha
  · intro ha
    rw [ha, map_zero]

end N25


noncomputable section
namespace N25

/-- Universal irreducibility equips the plane coordinate ring with its domain structure. -/
instance unitPlaneRing25C_domain (K : Type*) [Field K] : IsDomain (UnitPlaneRing25C K) :=
  unitPlaneRing25C_isDomain

/-- A plane point whose first coordinate is transcendental defines a map of function fields. -/
def unitPlaneFieldPointLift25C {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental K u) :
    UnitPlaneFF25C K →ₐ[K] F :=
  IsFractionRing.liftAlgHom (unitPlaneFieldPointEvaluation25C_injective (K := K) u v hr hu)

end N25


