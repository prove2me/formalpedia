-- Prove2me | Definitions.Def_FiniteFields_Dwork_ArtinHasse
-- name    : FiniteFields_Dwork_ArtinHasse
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T01:27:29.650854+00:00
-- url     : https://prove2.me/theorems/54c2fc5f-aa8f-4282-816d-eaca642082c4
-- title:
--   Signed Artin–Hasse exponential, ramified Frobenius and Dwork's splitting series $\theta(X)=E_p(\eta X)$
-- statement:
--   Let $k$ be a finite field of characteristic $p$, let $K_0$ be the completed fraction field of $W(k)$ with Frobenius $\sigma$, and let $L=K_0(\zeta)$ be its $p$-th cyclotomic extension, with primitive $p$-th root of unity $\zeta$ and $\lambda=\zeta-1$, all as in the foundations file. This file constructs the splitting series used in Dwork's additive character.
--
--   1. **Cyclotomic presentation.** $\mathcal O_{K_0}$ is the valuation ring of $K_0$, with uniformizer $p$. The shifted cyclotomic polynomial $\Phi_p(X+1)\in\mathcal O_{K_0}[X]$ is monic of degree $p-1$ and Eisenstein, and it presents $L$ as $K_0[X]/(\Phi_p)$ with root $\zeta$.
--   2. **Ramified Frobenius.** $\sigma_L$ is the unique ring automorphism of $L$ that extends $\sigma$ and fixes $\zeta$, together with the absolute value $x\mapsto\|\sigma_L(x)\|$ that it induces.
--   3. **Signed Artin–Hasse exponential.** A rational series is $p$-integral if all its coefficients lie in $\mathbb Z_{(p)}$. The series
--   $$E_p(X)=\exp\Big(-\sum_{j\ge0}\frac{X^{p^j}}{p^j}\Big)\in\mathbb Q[[X]]$$
--   is defined by formal substitution into $\exp$, with the logarithm $-\sum_j X^{p^j}/p^j$ given explicitly. Its image in $L[[X]]$ has coefficients of norm at most $1$.
--   4. **Evaluation on the open unit disc.** For $f=\sum_n c_nX^n\in L[[X]]$ and $x\in L$, the value is $f(x)=\sum_n c_nx^n$. Series with all $|c_n|\le1$ form a subring, and for $|x|<1$ evaluation at $x$ is a ring homomorphism on that subring.
--   5. **Dwork's parameter and splitting series.** $\eta\in L$ is the unique element with $|\eta|\le|\lambda|$, $|\eta|<1$ and $E_p(\eta)=\zeta$. The splitting series is
--   $$\theta(X)=E_p(\eta X)=\sum_{n\ge0}\theta_nX^n,\qquad |\theta_n|\le|\eta|^n .$$
--
--   The file also contains the structural lemmas used by these constructions: the Eisenstein property, the continuity and isometry of $\sigma_L$, the $p$-integrality of $E_p$, and the existence and uniqueness of $\eta$ in the stated disc.
--
--   The series $\theta$ plays the role of Dwork's $\theta(t)=F(t,\lambda)$ of §1. It is the analytic function whose values at Teichmüller representatives produce the additive character of $k$. The ramified Frobenius $\sigma_L$ is the coefficient Frobenius that later enters Dwork's operator.
--
--   **Formalization Note** The sign convention $E_p(X)=1-X+O(X^2)$ (the exponential of minus the Artin–Hasse logarithm) is the one used throughout the formalization. The parameter $\eta$ is chosen with `Exists.choose` from a proved existence-and-uniqueness statement, and it is new data, not definitionally $\lambda$. Evaluation is a `tsum`, which is only meaningful under the stated coefficient and radius bounds.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §1: Lemma 1 and the series $F(t,Y)$ of (2)–(4), $\theta(t)=F(t,\lambda)$ with $\operatorname{ord}\beta_m\ge m/(p-1)$ in (5)–(6), and the remark on the Artin–Hasse exponential $E(X)=\exp(\sum_j X^{p^j}/p^j)$. Lean: ported from the `finite_fields` project (commit e8b5bf14), modules `WeilConjectures/Dwork/CyclotomicPresentation.lean`, `WeilConjectures/Dwork/RamifiedFrobenius.lean`, `WeilConjectures/Dwork/ArtinHasse.lean`, `WeilConjectures/Dwork/AnalyticEvaluation.lean`, `WeilConjectures/Dwork/SplittingFunction.lean`.

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Foundations

section
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Polynomial
open scoped WithZero
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
 abbrev coefficientFieldValuation :
    Valuation (CoefficientField k p) ℤᵐ⁰ :=
  Valued.v
abbrev CoefficientIntegerRing :=
  (coefficientFieldValuation k p).integer
 theorem coefficientFieldValuation_p :
    coefficientFieldValuation k p (p : CoefficientField k p) =
      WithZero.exp (-1 : ℤ) := by
  rw [show (p : CoefficientField k p) =
      ((p : WithVal (coefficientValuation k p)) : CoefficientField k p) by
        exact (map_natCast
          (UniformSpace.Completion.coeRingHom :
            WithVal (coefficientValuation k p) →+* CoefficientField k p) p).symm]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p (p : CoefficientFractionField k p) = _
  rw [show (p : CoefficientFractionField k p) =
      algebraMap (CoefficientRing k p) (CoefficientFractionField k p) p by simp,
    coefficientValuation_p]
def coefficientIntegerUniformizer : CoefficientIntegerRing k p :=
  ⟨(p : CoefficientField k p), by
    rw [Valuation.mem_integer_iff]
    exact le_of_lt (by
      rw [coefficientFieldValuation_p k p, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)⟩
 theorem coefficientIntegerUniformizer_isUniformizer :
    (coefficientFieldValuation k p).IsUniformizer
      (coefficientIntegerUniformizer k p : CoefficientField k p) := by
  rw [Valuation.IsUniformizer.iff]
  change coefficientFieldValuation k p (p : CoefficientField k p) = _
  rw [coefficientFieldValuation_p]
  exact congrArg Units.val
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (coefficientFieldValuation_surjective k p)).symm
 theorem coefficientInteger_maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (CoefficientIntegerRing k p) =
      Ideal.span {coefficientIntegerUniformizer k p} := by
  exact Valuation.IsUniformizer.is_generator
    (coefficientIntegerUniformizer_isUniformizer k p)
def DworkShiftedCyclotomicPolynomial : (CoefficientIntegerRing k p)[X] :=
  (cyclotomic p (CoefficientIntegerRing k p)).comp (X + 1)
 theorem dworkShiftedCyclotomicPolynomial_monic :
    (DworkShiftedCyclotomicPolynomial k p).Monic := by
  simpa [DworkShiftedCyclotomicPolynomial] using
    (cyclotomic.monic p (CoefficientIntegerRing k p)).comp_X_add_C 1
 theorem dworkShiftedCyclotomicPolynomial_natDegree :
    (DworkShiftedCyclotomicPolynomial k p).natDegree = p - 1 := by
  rw [DworkShiftedCyclotomicPolynomial, natDegree_comp,
    natDegree_cyclotomic, Nat.totient_prime (Fact.out : Nat.Prime p),
    show (X + 1 : (CoefficientIntegerRing k p)[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one]
 theorem dworkShiftedCyclotomicPolynomial_coeff_zero :
    (DworkShiftedCyclotomicPolynomial k p).coeff 0 =
      coefficientIntegerUniformizer k p := by
  apply Subtype.ext
  simp only [DworkShiftedCyclotomicPolynomial, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime, eval_add, eval_X, eval_one, zero_add, eval_geom_sum,
    one_geom_sum, coefficientIntegerUniformizer]
  norm_cast
 theorem coefficientIntegerUniformizer_not_mem_maximalIdeal_sq :
    coefficientIntegerUniformizer k p ∉
      IsLocalRing.maximalIdeal (CoefficientIntegerRing k p) ^ 2 := by
  rw [coefficientInteger_maximalIdeal_eq_span, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  intro h
  rw [pow_two] at h
  obtain ⟨a, ha⟩ := h
  have hpi : coefficientIntegerUniformizer k p ≠ 0 := by
    intro hzero
    apply (coefficientIntegerUniformizer_isUniformizer k p).ne_zero
    simpa using congrArg Subtype.val hzero
  have ha_one : coefficientIntegerUniformizer k p * a = 1 := by
    apply mul_left_cancel₀ hpi
    simpa [mul_assoc] using ha.symm
  exact (coefficientIntegerUniformizer_isUniformizer k p).not_isUnit
    (isUnit_iff_exists_inv.mpr ⟨a, ha_one⟩)
theorem dworkShiftedCyclotomicPolynomial_isEisenstein :
    (DworkShiftedCyclotomicPolynomial k p).IsEisensteinAt
      (IsLocalRing.maximalIdeal (CoefficientIntegerRing k p)) := by
  refine (dworkShiftedCyclotomicPolynomial_monic k p).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top ?_ ?_
  · intro i hi
    rw [coefficientInteger_maximalIdeal_eq_span, Ideal.mem_span_singleton]
    rw [dworkShiftedCyclotomicPolynomial_natDegree] at hi
    have hip : i < p := hi.trans_le (Nat.sub_le _ _)
    have hcoeff : (DworkShiftedCyclotomicPolynomial k p).coeff i =
        (p.choose (i + 1) : CoefficientIntegerRing k p) := by
      rw [DworkShiftedCyclotomicPolynomial, cyclotomic_prime,
        geom_sum_X_comp_X_add_one_eq_sum, finsetSum_coeff]
      simp [hip]
    rw [hcoeff]
    obtain ⟨a, ha⟩ := (Fact.out : Nat.Prime p).dvd_choose_self i.succ_ne_zero
      (lt_tsub_iff_right.1 hi)
    refine ⟨(a : CoefficientIntegerRing k p), ?_⟩
    apply Subtype.ext
    simp [coefficientIntegerUniformizer, ha]
  · rw [dworkShiftedCyclotomicPolynomial_coeff_zero]
    exact coefficientIntegerUniformizer_not_mem_maximalIdeal_sq k p
 theorem dworkShiftedCyclotomicPolynomial_irreducible_integer :
    Irreducible (DworkShiftedCyclotomicPolynomial k p) := by
  apply (dworkShiftedCyclotomicPolynomial_isEisenstein k p).irreducible
  · exact (IsLocalRing.maximalIdeal.isMaximal
      (CoefficientIntegerRing k p)).isPrime
  · exact (dworkShiftedCyclotomicPolynomial_monic k p).isPrimitive
  · rw [dworkShiftedCyclotomicPolynomial_natDegree]
    exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
 theorem dworkShiftedCyclotomicPolynomial_map :
    (DworkShiftedCyclotomicPolynomial k p).map
        (algebraMap (CoefficientIntegerRing k p) (CoefficientField k p)) =
      (cyclotomic p (CoefficientField k p)).comp (X + 1) := by
  simp [DworkShiftedCyclotomicPolynomial, map_comp, map_cyclotomic]
 theorem dworkShiftedCyclotomicPolynomial_irreducible_field :
    Irreducible ((cyclotomic p (CoefficientField k p)).comp (X + 1)) := by
  have hirr : Irreducible ((DworkShiftedCyclotomicPolynomial k p).map
      (algebraMap (CoefficientIntegerRing k p) (CoefficientField k p))) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := CoefficientField k p) (dworkShiftedCyclotomicPolynomial_monic k p)).mp
        (dworkShiftedCyclotomicPolynomial_irreducible_integer k p)
  rwa [dworkShiftedCyclotomicPolynomial_map] at hirr
theorem dworkCyclotomicPolynomial_irreducible :
    Irreducible (DworkCyclotomicPolynomial k p) := by
  have hshift := dworkShiftedCyclotomicPolynomial_irreducible_field k p
  have hmap : Irreducible
      ((Polynomial.algEquivAevalXAddC (1 : CoefficientField k p)).toMulEquiv
        (cyclotomic p (CoefficientField k p))) := by
    simpa [← comp_eq_aeval] using hshift
  have hirr := MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalXAddC (1 : CoefficientField k p)).toMulEquiv |>.mp hmap
  simpa [DworkCyclotomicPolynomial] using hirr
theorem dworkPrimitiveRoot_minpoly :
    minpoly (CoefficientField k p) (dworkPrimitiveRoot k p) =
      DworkCyclotomicPolynomial k p := by
  simpa [DworkCyclotomicPolynomial] using
    ((dworkPrimitiveRoot_isPrimitiveRoot k p).minpoly_eq_cyclotomic_of_irreducible
      (by simpa [DworkCyclotomicPolynomial] using
        dworkCyclotomicPolynomial_irreducible k p)).symm
theorem dworkPrimitiveRoot_adjoin_eq_top :
    Algebra.adjoin (CoefficientField k p) {dworkPrimitiveRoot k p} = ⊤ :=
  IsCyclotomicExtension.adjoin_primitive_root_eq_top
    (dworkPrimitiveRoot_isPrimitiveRoot k p)
noncomputable def dworkCyclotomicIsAdjoinRoot :
    IsAdjoinRoot (DworkCyclotomicField k p) (DworkCyclotomicPolynomial k p) :=
  let hα := (IsCyclotomicExtension.integral ({p} : Set ℕ)
    (CoefficientField k p) (DworkCyclotomicField k p)).isIntegral
      (dworkPrimitiveRoot k p)
  let h := IsAdjoinRoot.mkOfAdjoinEqTop hα (dworkPrimitiveRoot_adjoin_eq_top k p)
  { map := h.map
    map_surjective := h.map_surjective
    ker_map := by
      simpa [dworkPrimitiveRoot_minpoly k p] using h.ker_map }
@[simp]
theorem dworkCyclotomicIsAdjoinRoot_root :
    (dworkCyclotomicIsAdjoinRoot k p).root = dworkPrimitiveRoot k p := by
  change aeval (dworkPrimitiveRoot k p) X = dworkPrimitiveRoot k p
  simp
end FiniteFields.Dwork
end
end

section
noncomputable section
open Polynomial
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
 abbrev coefficientToCyclotomic :
    CoefficientField k p →+* DworkCyclotomicField k p :=
  algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
theorem dworkCyclotomicPolynomial_map_coefficientFieldFrobenius :
    (DworkCyclotomicPolynomial k p).map (coefficientFieldFrobenius k p).toRingHom =
      DworkCyclotomicPolynomial k p := by
  simp [DworkCyclotomicPolynomial, map_cyclotomic]
 theorem dworkCyclotomicPolynomial_map_coefficientFieldFrobenius_symm :
    (DworkCyclotomicPolynomial k p).map
        (coefficientFieldFrobenius k p).symm.toRingHom =
      DworkCyclotomicPolynomial k p := by
  simp [DworkCyclotomicPolynomial, map_cyclotomic]
theorem dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius :
    (DworkCyclotomicPolynomial k p).eval₂
        ((coefficientToCyclotomic k p).comp
          (coefficientFieldFrobenius k p).toRingHom)
        (dworkPrimitiveRoot k p) = 0 := by
  rw [eval₂_eq_eval_map, ← map_map,
    dworkCyclotomicPolynomial_map_coefficientFieldFrobenius]
  rw [← eval₂_eq_eval_map, ← aeval_def]
  rw [← dworkCyclotomicIsAdjoinRoot_root k p]
  exact (dworkCyclotomicIsAdjoinRoot k p).aeval_root_self
 theorem dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius_symm :
    (DworkCyclotomicPolynomial k p).eval₂
        ((coefficientToCyclotomic k p).comp
          (coefficientFieldFrobenius k p).symm.toRingHom)
        (dworkPrimitiveRoot k p) = 0 := by
  rw [eval₂_eq_eval_map, ← map_map,
    dworkCyclotomicPolynomial_map_coefficientFieldFrobenius_symm]
  rw [← eval₂_eq_eval_map, ← aeval_def]
  rw [← dworkCyclotomicIsAdjoinRoot_root k p]
  exact (dworkCyclotomicIsAdjoinRoot k p).aeval_root_self
def ramifiedCoefficientFrobeniusHom :
    DworkCyclotomicField k p →+* DworkCyclotomicField k p :=
  (dworkCyclotomicIsAdjoinRoot k p).lift
    ((coefficientToCyclotomic k p).comp (coefficientFieldFrobenius k p).toRingHom)
    (dworkPrimitiveRoot k p)
    (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius k p)
def ramifiedCoefficientFrobeniusInvHom :
    DworkCyclotomicField k p →+* DworkCyclotomicField k p :=
  (dworkCyclotomicIsAdjoinRoot k p).lift
    ((coefficientToCyclotomic k p).comp (coefficientFieldFrobenius k p).symm.toRingHom)
    (dworkPrimitiveRoot k p)
    (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius_symm k p)
 theorem ramifiedCoefficientFrobeniusHom_algebraMap
    (a : CoefficientField k p) :
    ramifiedCoefficientFrobeniusHom k p
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (coefficientFieldFrobenius k p a) := by
  exact (dworkCyclotomicIsAdjoinRoot k p).lift_algebraMap
    (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius k p) a
 theorem ramifiedCoefficientFrobeniusInvHom_algebraMap
    (a : CoefficientField k p) :
    ramifiedCoefficientFrobeniusInvHom k p
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        ((coefficientFieldFrobenius k p).symm a) := by
  exact (dworkCyclotomicIsAdjoinRoot k p).lift_algebraMap
    (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius_symm k p) a
 theorem ramifiedCoefficientFrobeniusHom_dworkPrimitiveRoot :
    ramifiedCoefficientFrobeniusHom k p (dworkPrimitiveRoot k p) =
      dworkPrimitiveRoot k p := by
  simpa only [ramifiedCoefficientFrobeniusHom,
    dworkCyclotomicIsAdjoinRoot_root] using
    (dworkCyclotomicIsAdjoinRoot k p).lift_root
      (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius k p)
 theorem ramifiedCoefficientFrobeniusInvHom_dworkPrimitiveRoot :
    ramifiedCoefficientFrobeniusInvHom k p (dworkPrimitiveRoot k p) =
      dworkPrimitiveRoot k p := by
  simpa only [ramifiedCoefficientFrobeniusInvHom,
    dworkCyclotomicIsAdjoinRoot_root] using
    (dworkCyclotomicIsAdjoinRoot k p).lift_root
      (dworkCyclotomicPolynomial_eval₂_coefficientFieldFrobenius_symm k p)
 theorem dworkCyclotomicPolynomial_eval₂_algebraMap :
    (DworkCyclotomicPolynomial k p).eval₂ (coefficientToCyclotomic k p)
        (dworkPrimitiveRoot k p) = 0 := by
  rw [← aeval_def, ← dworkCyclotomicIsAdjoinRoot_root k p]
  exact (dworkCyclotomicIsAdjoinRoot k p).aeval_root_self
 theorem ramifiedCoefficientFrobeniusHom_comp_invHom :
    (ramifiedCoefficientFrobeniusHom k p).comp
        (ramifiedCoefficientFrobeniusInvHom k p) =
      RingHom.id (DworkCyclotomicField k p) := by
  let h := dworkCyclotomicIsAdjoinRoot k p
  let hz := dworkCyclotomicPolynomial_eval₂_algebraMap k p
  calc
    (ramifiedCoefficientFrobeniusHom k p).comp
        (ramifiedCoefficientFrobeniusInvHom k p) =
        h.lift (coefficientToCyclotomic k p) (dworkPrimitiveRoot k p) hz :=
      h.eq_lift hz _ (fun a => by
        simp only [RingHom.comp_apply, ramifiedCoefficientFrobeniusInvHom_algebraMap,
          ramifiedCoefficientFrobeniusHom_algebraMap, RingEquiv.apply_symm_apply]) (by
        simp only [h, RingHom.comp_apply, dworkCyclotomicIsAdjoinRoot_root,
          ramifiedCoefficientFrobeniusInvHom_dworkPrimitiveRoot,
          ramifiedCoefficientFrobeniusHom_dworkPrimitiveRoot])
    _ = RingHom.id (DworkCyclotomicField k p) :=
      (h.eq_lift hz _ (fun a => by simp) (by
        simp only [h, RingHom.id_apply, dworkCyclotomicIsAdjoinRoot_root])).symm
 theorem ramifiedCoefficientFrobeniusInvHom_comp_hom :
    (ramifiedCoefficientFrobeniusInvHom k p).comp
        (ramifiedCoefficientFrobeniusHom k p) =
      RingHom.id (DworkCyclotomicField k p) := by
  let h := dworkCyclotomicIsAdjoinRoot k p
  let hz := dworkCyclotomicPolynomial_eval₂_algebraMap k p
  calc
    (ramifiedCoefficientFrobeniusInvHom k p).comp
        (ramifiedCoefficientFrobeniusHom k p) =
        h.lift (coefficientToCyclotomic k p) (dworkPrimitiveRoot k p) hz :=
      h.eq_lift hz _ (fun a => by
        simp only [RingHom.comp_apply, ramifiedCoefficientFrobeniusHom_algebraMap,
          ramifiedCoefficientFrobeniusInvHom_algebraMap, RingEquiv.symm_apply_apply]) (by
        simp only [h, RingHom.comp_apply, dworkCyclotomicIsAdjoinRoot_root,
          ramifiedCoefficientFrobeniusHom_dworkPrimitiveRoot,
          ramifiedCoefficientFrobeniusInvHom_dworkPrimitiveRoot])
    _ = RingHom.id (DworkCyclotomicField k p) :=
      (h.eq_lift hz _ (fun a => by simp) (by
        simp only [h, RingHom.id_apply, dworkCyclotomicIsAdjoinRoot_root])).symm
def ramifiedCoefficientFrobenius :
    DworkCyclotomicField k p ≃+* DworkCyclotomicField k p :=
  RingEquiv.ofRingHom
    (ramifiedCoefficientFrobeniusHom k p)
    (ramifiedCoefficientFrobeniusInvHom k p)
    (ramifiedCoefficientFrobeniusHom_comp_invHom k p)
    (ramifiedCoefficientFrobeniusInvHom_comp_hom k p)
@[simp]
theorem ramifiedCoefficientFrobenius_algebraMap (a : CoefficientField k p) :
    ramifiedCoefficientFrobenius k p
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (coefficientFieldFrobenius k p a) := by
  exact ramifiedCoefficientFrobeniusHom_algebraMap k p a
theorem coefficientFieldFrobenius_norm (x : CoefficientField k p) :
    ‖coefficientFieldFrobenius k p x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      (continuous_norm.comp (coefficientFieldFrobenius_continuous k p)) continuous_norm) ?_
  intro y
  rw [coefficientFieldFrobenius_coe]
  apply le_antisymm
  · rw [Valued.toNormedField.norm_le_iff]
    rw [Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
    change coefficientValuation k p
        (WittVector.FractionRing.frobenius p k y.ofVal) ≤ coefficientValuation k p y.ofVal
    exact (coefficientValuation_frobenius k p y.ofVal).le
  · rw [Valued.toNormedField.norm_le_iff]
    rw [Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
    change coefficientValuation k p y.ofVal ≤ coefficientValuation k p
        (WittVector.FractionRing.frobenius p k y.ofVal)
    exact (coefficientValuation_frobenius k p y.ofVal).ge
def ramifiedCoefficientFrobeniusAbsoluteValue :
    AbsoluteValue (DworkCyclotomicField k p) ℝ where
  toFun x := ‖ramifiedCoefficientFrobenius k p x‖
  map_mul' x y := by rw [map_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    rw [map_add]
    exact norm_add_le _ _
theorem ramifiedCoefficientFrobeniusAbsoluteValue_extends (a : CoefficientField k p) :
    ramifiedCoefficientFrobeniusAbsoluteValue k p
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a) = ‖a‖ := by
  change ‖ramifiedCoefficientFrobenius k p
      (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a)‖ = ‖a‖
  rw [ramifiedCoefficientFrobenius_algebraMap,
    dworkCyclotomicField_norm_algebraMap, coefficientFieldFrobenius_norm]
theorem ramifiedCoefficientFrobenius_norm (x : DworkCyclotomicField k p) :
    ‖ramifiedCoefficientFrobenius k p x‖ = ‖x‖ := by
  change ramifiedCoefficientFrobeniusAbsoluteValue k p x = ‖x‖
  calc
    ramifiedCoefficientFrobeniusAbsoluteValue k p x =
        spectralNorm (CoefficientField k p) (DworkCyclotomicField k p) x :=
      spectralNorm_unique_field_norm_ext
        (ramifiedCoefficientFrobeniusAbsoluteValue_extends k p) x
    _ = ‖x‖ :=
      (NormedAlgebra.norm_eq_spectralNorm (CoefficientField k p) x).symm
theorem ramifiedCoefficientFrobenius_symm_norm (x : DworkCyclotomicField k p) :
    ‖(ramifiedCoefficientFrobenius k p).symm x‖ = ‖x‖ := by
  calc
    ‖(ramifiedCoefficientFrobenius k p).symm x‖ =
        ‖ramifiedCoefficientFrobenius k p
          ((ramifiedCoefficientFrobenius k p).symm x)‖ :=
      (ramifiedCoefficientFrobenius_norm k p _).symm
    _ = ‖x‖ := by rw [(ramifiedCoefficientFrobenius k p).apply_symm_apply]
theorem ramifiedCoefficientFrobenius_symm_isometry :
    Isometry (ramifiedCoefficientFrobenius k p).symm :=
  AddMonoidHomClass.isometry_of_norm _ (ramifiedCoefficientFrobenius_symm_norm k p)
theorem ramifiedCoefficientFrobenius_symm_continuous :
    Continuous (ramifiedCoefficientFrobenius k p).symm :=
  (ramifiedCoefficientFrobenius_symm_isometry k p).continuous
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter PowerSeries
open scoped Classical NNReal Topology Valued
namespace FiniteFields.Dwork
variable (p : ℕ) [Fact p.Prime]
def IsPIntegralPowerSeries (f : ℚ⟦X⟧) : Prop :=
  ∀ n, Rat.padicValuation p (PowerSeries.coeff n f) ≤ 1
def IsPDivisibleOffConstant (f : ℚ⟦X⟧) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧
    ∀ n, n ≠ 0 → ∃ a : ℚ,
      Rat.padicValuation p a ≤ 1 ∧ PowerSeries.coeff n f = (p : ℚ) * a
def artinHasseLog : ℚ⟦X⟧ :=
  by
    classical
    exact PowerSeries.mk fun n => if ∃ j : ℕ, p ^ j = n then -(1 / (n : ℚ)) else 0
omit [Fact p.Prime] in
theorem artinHasseLog_coeff (n : ℕ) :
    PowerSeries.coeff n (artinHasseLog p) =
      if ∃ j : ℕ, p ^ j = n then -(1 / (n : ℚ)) else 0 :=
  by
    classical
    exact PowerSeries.coeff_mk _ _
omit [Fact p.Prime] in
theorem artinHasseLog_coeff_primePower (j : ℕ) :
    PowerSeries.coeff (p ^ j) (artinHasseLog p) = -(1 / (p ^ j : ℚ)) := by
  rw [artinHasseLog_coeff]
  simp
omit [Fact p.Prime] in
@[simp]
theorem artinHasseLog_constantCoeff :
    PowerSeries.constantCoeff (artinHasseLog p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, artinHasseLog_coeff]
  simp
omit [Fact p.Prime] in
 theorem artinHasseLog_hasSubst : PowerSeries.HasSubst (artinHasseLog p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (artinHasseLog_constantCoeff p)
def artinHasseExponential : ℚ⟦X⟧ :=
  (PowerSeries.exp ℚ).subst (artinHasseLog p)
 def formalExponential (g : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  (PowerSeries.exp ℚ).subst g
 theorem formalExponential_constantCoeff {g : ℚ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (formalExponential g) = 1 := by
  change PowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst g) = 1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hd, hg]
omit [Fact p.Prime] in
@[simp]
theorem artinHasseExponential_constantCoeff :
    PowerSeries.constantCoeff (artinHasseExponential p) = 1 := by
  exact formalExponential_constantCoeff (artinHasseLog_constantCoeff p)
 theorem formalExponential_derivative {g : ℚ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.derivative ℚ (formalExponential g) =
      formalExponential g * PowerSeries.derivative ℚ g := by
  rw [formalExponential, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg), PowerSeries.derivative_exp]
 theorem powerSeries_eq_of_derivative_eq_mul
    {f g h : ℚ⟦X⟧}
    (hf : PowerSeries.derivative ℚ f = f * h)
    (hg : PowerSeries.derivative ℚ g = g * h)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g) :
    f = g := by
  exact PowerSeries.eq_of_derivative_eq_mul hf hg h0
 theorem formalExponential_add {g h : ℚ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0) :
    formalExponential (g + h) = formalExponential g * formalExponential h := by
  apply powerSeries_eq_of_derivative_eq_mul
      (h := PowerSeries.derivative ℚ (g + h))
  · rw [formalExponential_derivative (by simp [hg, hh])]
  · rw [map_add,
      (PowerSeries.derivative ℚ).leibniz,
      formalExponential_derivative hg,
      formalExponential_derivative hh]
    ring
  · simp [formalExponential_constantCoeff, hg, hh]
 theorem formalExponential_nsmul {g : ℚ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    formalExponential (n • g) = formalExponential g ^ n := by
  induction n with
  | zero =>
      rw [zero_nsmul, pow_zero]
      change (PowerSeries.exp ℚ).subst 0 = 1
      calc
        (PowerSeries.exp ℚ).subst 0 =
            PowerSeries.rescale 0 (PowerSeries.exp ℚ) := by
              rw [PowerSeries.rescale_eq_subst]
              simp
        _ = 1 := by simp
  | succ n ih =>
      rw [succ_nsmul, formalExponential_add (by simp [hg]) hg, ih, pow_succ]
 theorem artinHasseLog_frobenius_difference :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero (artinHasseLog p) -
        p • artinHasseLog p = PowerSeries.C (p : ℚ) * PowerSeries.X := by
  ext n
  rw [map_sub, PowerSeries.coeff_expand,
    map_nsmul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  by_cases hn0 : n = 0
  · subst n
    simp [artinHasseLog_coeff]
  by_cases hn1 : n = 1
  · subst n
    have hpd : ¬p ∣ 1 := by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one
    simp [hpd, artinHasseLog_coeff]
  have hn_gt_one : 1 < n := by omega
  by_cases hnPow : ∃ j : ℕ, p ^ j = n
  · obtain ⟨j, hj⟩ := hnPow
    obtain _ | j := j
    · exact (hn1 hj.symm).elim
    · have hpd : p ∣ n := by
        refine ⟨p ^ j, ?_⟩
        rw [← hj, pow_succ, Nat.mul_comm]
      have hdiv : n / p = p ^ j := by
        rw [← hj, pow_succ', Nat.mul_div_cancel_left _
          (Fact.out : Nat.Prime p).pos]
      rw [if_pos hpd, hdiv, artinHasseLog_coeff_primePower,
        artinHasseLog_coeff]
      rw [if_pos ⟨j + 1, hj⟩]
      simp only [hn1, if_false, mul_zero, nsmul_eq_mul]
      rw [← hj]
      have hpq : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      field_simp [pow_succ, hpq]
      simp [pow_succ]
  · have hnCoeff : PowerSeries.coeff n (artinHasseLog p) = 0 := by
      simp [artinHasseLog_coeff, hnPow]
    by_cases hpd : p ∣ n
    · have hquotPow : ¬ ∃ j : ℕ, p ^ j = n / p := by
        rintro ⟨j, hj⟩
        apply hnPow
        refine ⟨j + 1, ?_⟩
        rw [pow_succ, hj, Nat.div_mul_cancel hpd]
      rw [if_pos hpd, hnCoeff]
      simp only [smul_zero, sub_zero]
      rw [artinHasseLog_coeff]
      simp [hquotPow, hn1]
    · simp [hpd, hnCoeff, hn1]
 theorem artinHasse_expand_exponential :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
        (artinHasseExponential p) =
      formalExponential
        (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero (artinHasseLog p)) := by
  rw [artinHasseExponential, formalExponential]
  change MvPowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
      ((PowerSeries.exp ℚ).subst (artinHasseLog p)) =
    (PowerSeries.exp ℚ).subst
      (MvPowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero (artinHasseLog p))
  exact PowerSeries.expand_subst p (Fact.out : Nat.Prime p).ne_zero
    (artinHasseLog_hasSubst p) (PowerSeries.exp ℚ)
omit [Fact p.Prime] in
 theorem artinHasse_power_exponential :
    artinHasseExponential p ^ p = formalExponential (p • artinHasseLog p) := by
  rw [artinHasseExponential, ← formalExponential]
  exact (formalExponential_nsmul (artinHasseLog_constantCoeff p) p).symm
theorem artinHasse_frobeniusQuotient :
    PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
          (artinHasseExponential p) *
        (artinHasseExponential p ^ p)⁻¹ =
      PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ) := by
  rw [artinHasse_expand_exponential, artinHasse_power_exponential,
    sub_eq_iff_eq_add.mp (artinHasseLog_frobenius_difference p)]
  have hzero : PowerSeries.constantCoeff
      (PowerSeries.C (p : ℚ) * PowerSeries.X) = 0 := by simp
  rw [formalExponential_add hzero (by simp)]
  have hunit : PowerSeries.constantCoeff
      (formalExponential (p • artinHasseLog p)) ≠ 0 := by
    rw [formalExponential_constantCoeff (by simp)]
    exact one_ne_zero
  rw [mul_assoc, PowerSeries.mul_inv_cancel _ hunit, mul_one]
  rw [formalExponential, PowerSeries.rescale_eq_subst]
  congr 1
  simp [smul_eq_C_mul]
 abbrev PLocalInteger : Type :=
  Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))
 def pLocalIntegerToRat : PLocalInteger p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl)
    (g := Int.castRingHom ℚ) fun s => by
      apply isUnit_iff_ne_zero.mpr
      change (s.val : ℚ) ≠ 0
      intro hs
      have hs' : s.val = 0 := by exact_mod_cast hs
      exact s.property (hs' ▸ Ideal.zero_mem _)
 theorem pLocalIntegerToRat_apply_algebraMap (z : ℤ) :
    pLocalIntegerToRat p (algebraMap ℤ (PLocalInteger p) z) = (z : ℚ) := by
  exact IsLocalization.lift_eq _ z
 theorem pLocalIntegerToRat_injective :
    Function.Injective (pLocalIntegerToRat p) := by
  unfold pLocalIntegerToRat
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro h
    have h' := congrArg (pLocalIntegerToRat p) h
    rw [pLocalIntegerToRat_apply_algebraMap,
      pLocalIntegerToRat_apply_algebraMap] at h'
    exact h'
  · intro h
    change (a : ℚ) = (b : ℚ) at h
    exact congrArg (algebraMap ℤ (PLocalInteger p)) (Int.cast_injective h)
 theorem pLocalIntegerToRat_isPIntegral (x : PLocalInteger p) :
    Rat.padicValuation p (pLocalIntegerToRat p x) ≤ 1 := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl x
  rw [pLocalIntegerToRat, IsLocalization.lift_mk']
  simp only [Units.val_inv_eq_inv_val, IsUnit.coe_liftRight]
  rw [map_mul, map_inv₀]
  change Rat.padicValuation p (a : ℚ) *
      (Rat.padicValuation p (s.val : ℚ))⁻¹ ≤ 1
  have hsval : Int.padicValuation p s = 1 := by
    rw [Int.padicValuation_eq_one_iff]
    intro hdiv
    exact s.property (Ideal.mem_span_singleton.mpr hdiv)
  rw [Rat.padicValuation_cast, Rat.padicValuation_cast, hsval, inv_one,
    mul_one]
  exact Int.padicValuation_le_one p a
 theorem exists_pLocalIntegerToRat_of_isPIntegral {q : ℚ}
    (hq : Rat.padicValuation p q ≤ 1) :
    ∃ x : PLocalInteger p, pLocalIntegerToRat p x = q := by
  have hden : ¬p ∣ q.den := Rat.padicValuation_le_one_iff.mp hq
  let s : (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl :=
    ⟨(q.den : ℤ), by
      change (q.den : ℤ) ∉ Ideal.span ({(p : ℤ)} : Set ℤ)
      rw [Ideal.mem_span_singleton]
      simpa only [Int.natCast_dvd_natCast] using hden⟩
  refine ⟨IsLocalization.mk' (PLocalInteger p) q.num s, ?_⟩
  rw [pLocalIntegerToRat, IsLocalization.lift_mk']
  simp only [Units.val_inv_eq_inv_val, IsUnit.coe_liftRight]
  change (q.num : ℚ) * (q.den : ℚ)⁻¹ = q
  rw [← div_eq_mul_inv, q.num_div_den]
 theorem isPIntegral_iff_exists_pLocalInteger (q : ℚ) :
    Rat.padicValuation p q ≤ 1 ↔
      ∃ x : PLocalInteger p, pLocalIntegerToRat p x = q :=
  ⟨exists_pLocalIntegerToRat_of_isPIntegral p,
    fun ⟨x, hx⟩ => hx ▸ pLocalIntegerToRat_isPIntegral p x⟩
 abbrev PLocalMaximalIdeal : Ideal (PLocalInteger p) :=
  Ideal.span ({(p : PLocalInteger p)} : Set (PLocalInteger p))
 theorem pLocal_prime_mem_nonunits :
    (p : PLocalInteger p) ∈ nonunits (PLocalInteger p) := by
  rw [mem_nonunits_iff]
  rw [show (p : PLocalInteger p) =
    algebraMap ℤ (PLocalInteger p) (p : ℤ) by simp]
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (PLocalInteger p)
    (Ideal.span ({(p : ℤ)} : Set ℤ))]
  exact fun hpnotmem => hpnotmem (Ideal.mem_span_singleton_self (p : ℤ))
 noncomputable instance pLocalResidueCharP :
    CharP (PLocalInteger p ⧸ PLocalMaximalIdeal p) p :=
  CharP.quotient (PLocalInteger p) p (pLocal_prime_mem_nonunits p)
 theorem pLocalResidue_frobenius (x : PLocalInteger p) :
    frobenius (PLocalInteger p ⧸ PLocalMaximalIdeal p) p
        (Ideal.Quotient.mk (PLocalMaximalIdeal p) x) =
      Ideal.Quotient.mk (PLocalMaximalIdeal p) x := by
  let q : PLocalInteger p →+* (PLocalInteger p ⧸ PLocalMaximalIdeal p) :=
    Ideal.Quotient.mk (PLocalMaximalIdeal p)
  have hhom : (frobenius (PLocalInteger p ⧸ PLocalMaximalIdeal p) p).comp q = q := by
    apply IsLocalization.ringHom_ext
      (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl
    ext z
    simp [q]
  exact DFunLike.congr_fun hhom x
 theorem pLocal_frobeniusCoefficientDivisible
    (F : (PLocalInteger p)⟦X⟧) (n : ℕ) :
    ∃ b : PLocalInteger p,
      PowerSeries.coeff n
          (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero F - F ^ p) =
        (p : PLocalInteger p) * b := by
  let q : PLocalInteger p →+* (PLocalInteger p ⧸ PLocalMaximalIdeal p) :=
    Ideal.Quotient.mk (PLocalMaximalIdeal p)
  have hfrob : frobenius (PLocalInteger p ⧸ PLocalMaximalIdeal p) p = RingHom.id _ := by
    ext x
    exact pLocalResidue_frobenius p x
  have hseries : PowerSeries.map q
      (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero F - F ^ p) = 0 := by
    change MvPowerSeries.map q
      (MvPowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero F - F ^ p) = 0
    rw [map_sub, map_pow, MvPowerSeries.map_expand]
    have h := MvPowerSeries.map_frobenius_expand p
      (Fact.out : Nat.Prime p).ne_zero
      (f := MvPowerSeries.map q (F : MvPowerSeries Unit (PLocalInteger p)))
    rw [hfrob] at h
    simpa using sub_eq_zero.mpr h
  have hmem : PowerSeries.coeff n
      (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero F - F ^ p) ∈
        PLocalMaximalIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (PowerSeries.coeff n) hseries
    simpa only [PowerSeries.coeff_map, map_zero] using this
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [mul_comm]; exact hb.symm⟩
 theorem exists_pLocalDivisorSeries {g : ℚ⟦X⟧}
    (hg : IsPDivisibleOffConstant p g) :
    ∃ G : (PLocalInteger p)⟦X⟧,
      PowerSeries.constantCoeff G = 0 ∧
        g = 1 + PowerSeries.C (p : ℚ) *
          PowerSeries.map (pLocalIntegerToRat p) G := by
  have hex (n : ℕ) (hn : n ≠ 0) :
      ∃ x : PLocalInteger p,
        PowerSeries.coeff n g = (p : ℚ) * pLocalIntegerToRat p x := by
    obtain ⟨a, ha, hcoeff⟩ := hg.2 n hn
    obtain ⟨x, hx⟩ := (isPIntegral_iff_exists_pLocalInteger p a).mp ha
    exact ⟨x, hx ▸ hcoeff⟩
  let c : ℕ → PLocalInteger p := fun n =>
    if hn : n = 0 then 0 else (hex n hn).choose
  let G : (PLocalInteger p)⟦X⟧ := PowerSeries.mk c
  refine ⟨G, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [G, c]
  · ext n
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map]
    by_cases hn : n = 0
    · subst n
      simp [hg.1, G, c]
    · rw [if_neg hn, zero_add, PowerSeries.coeff_mk]
      rw [show c n = (hex n hn).choose by simp [c, hn]]
      change PowerSeries.coeff n g =
        (p : ℚ) * pLocalIntegerToRat p (hex n hn).choose
      exact (hex n hn).choose_spec
 theorem coeff_pow_eq_of_coeff_eq_up_to
    {A : Type*} [CommSemiring A] {f g : A⟦X⟧} {n : ℕ}
    (hfg : ∀ i ≤ n, PowerSeries.coeff i f = PowerSeries.coeff i g)
    (r : ℕ) :
    PowerSeries.coeff n (f ^ r) = PowerSeries.coeff n (g ^ r) := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨a, b⟩ hab
      rw [ih (n := a)
          (fun i hi => hfg i (hi.trans (Finset.HasAntidiagonal.antidiagonal.fst_le hab))),
        hfg b (Finset.HasAntidiagonal.antidiagonal.snd_le hab)]
 theorem coeff_mul_eq_of_constantCoeff_left_zero
    {A : Type*} [CommSemiring A] {u f g : A⟦X⟧} {n : ℕ}
    (hu : PowerSeries.constantCoeff u = 0)
    (hfg : ∀ j < n, PowerSeries.coeff j f = PowerSeries.coeff j g) :
    PowerSeries.coeff n (u * f) = PowerSeries.coeff n (u * g) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  by_cases ha : a = 0
  · subst a
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hu]
  · rw [hfg b]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    omega
omit [Fact p.Prime] in
 theorem coeff_pow_add_monomial
    (F : ℚ⟦X⟧) (hF : PowerSeries.constantCoeff F = 1)
    {n : ℕ} (hn : n ≠ 0) (a : ℚ) :
    PowerSeries.coeff n ((F + PowerSeries.monomial n a) ^ p) =
      (p : ℚ) * a + PowerSeries.coeff n (F ^ p) := by
  let A := F + PowerSeries.monomial n a
  let G := ∑ i ∈ Finset.range p, A ^ i * F ^ (p - 1 - i)
  have hmon0 : PowerSeries.constantCoeff (PowerSeries.monomial n a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_monomial,
      if_neg hn.symm]
  have hA : PowerSeries.constantCoeff A = 1 := by
    simp [A, hF, hmon0]
  have hG : PowerSeries.constantCoeff G = (p : ℚ) := by
    simp [G, hA, hF]
  have hid : (A - F) * G = A ^ p - F ^ p :=
    (Commute.all A F).mul_geom_sum₂ p
  have hsub : A - F = PowerSeries.monomial n a := by
    simp [A]
  have hm : PowerSeries.monomial n a = PowerSeries.C a * PowerSeries.X ^ n := by
    ext m
    rw [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul_X_pow]
  have hmono : PowerSeries.coeff n (PowerSeries.monomial n a * G) = a * (p : ℚ) := by
    rw [hm, mul_assoc, PowerSeries.coeff_C_mul]
    have hshift := PowerSeries.coeff_X_pow_mul G n 0
    simp only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] at hshift
    rw [hshift, hG]
  have hcoeff := congrArg (PowerSeries.coeff n) hid
  rw [hsub, hmono, map_sub] at hcoeff
  linarith
theorem dworkIntegralityCriterion {f : ℚ⟦X⟧}
    (h0 : PowerSeries.constantCoeff f = 1)
    (hquot : IsPDivisibleOffConstant p
      (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero f * (f ^ p)⁻¹)) :
    IsPIntegralPowerSeries p f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        rw [PowerSeries.coeff_zero_eq_constantCoeff, h0]
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let q := PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero f * (f ^ p)⁻¹
        obtain ⟨G, hG0, hqG⟩ := exists_pLocalDivisorSeries p hquot
        have hlift (i : ℕ) (hi : i < n) :
            ∃ x : PLocalInteger p, pLocalIntegerToRat p x = PowerSeries.coeff i f :=
          (isPIntegral_iff_exists_pLocalInteger p (PowerSeries.coeff i f)).mp (ih i hi)
        let c : ℕ → PLocalInteger p := fun i =>
          if hi : i < n then (hlift i hi).choose else 0
        let F : (PLocalInteger p)⟦X⟧ := PowerSeries.mk c
        let Fq : ℚ⟦X⟧ := PowerSeries.map (pLocalIntegerToRat p) F
        have hFq_lt (i : ℕ) (hi : i < n) :
            PowerSeries.coeff i Fq = PowerSeries.coeff i f := by
          dsimp [Fq, F]
          rw [PowerSeries.coeff_mk]
          rw [show c i = (hlift i hi).choose by simp [c, hi]]
          exact (hlift i hi).choose_spec
        have hF_n : PowerSeries.coeff n F = 0 := by
          dsimp [F]
          rw [PowerSeries.coeff_mk]
          simp [c]
        have hFq_n : PowerSeries.coeff n Fq = 0 := by
          dsimp [Fq]
          rw [hF_n, map_zero]
        have hF0 : PowerSeries.constantCoeff F = 1 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff]
          apply pLocalIntegerToRat_injective p
          rw [map_one]
          rw [← PowerSeries.coeff_map]
          change PowerSeries.coeff 0 Fq = 1
          rw [hFq_lt 0 hnpos, PowerSeries.coeff_zero_eq_constantCoeff, h0]
        have hFq0 : PowerSeries.constantCoeff Fq = 1 := by
          dsimp [Fq]
          rw [← PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, hF0, map_one]
        have hpow_lt (j : ℕ) (hj : j < n) :
            PowerSeries.coeff j (f ^ p) = PowerSeries.coeff j (Fq ^ p) := by
          apply coeff_pow_eq_of_coeff_eq_up_to (r := p)
          intro i hi
          exact (hFq_lt i (hi.trans_lt hj)).symm
        have hGq0 : PowerSeries.constantCoeff
            (PowerSeries.map (pLocalIntegerToRat p) G) = 0 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
            PowerSeries.coeff_zero_eq_constantCoeff, hG0, map_zero]
        have hcorrection : PowerSeries.coeff n
              (PowerSeries.map (pLocalIntegerToRat p) G * (f ^ p)) =
            PowerSeries.coeff n
              (PowerSeries.map (pLocalIntegerToRat p) G * (Fq ^ p)) :=
          coeff_mul_eq_of_constantCoeff_left_zero hGq0 hpow_lt
        have hfp0 : PowerSeries.constantCoeff (f ^ p) ≠ 0 := by
          rw [map_pow, h0, one_pow]
          exact one_ne_zero
        have hqmul : q * f ^ p =
            PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero f := by
          dsimp [q]
          rw [mul_assoc, PowerSeries.inv_mul_cancel _ hfp0, mul_one]
        have hqG' : q = 1 + PowerSeries.C (p : ℚ) *
            PowerSeries.map (pLocalIntegerToRat p) G := by
          simpa [q] using hqG
        have hexpand :
            PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero f =
              f ^ p + PowerSeries.C (p : ℚ) *
                (PowerSeries.map (pLocalIntegerToRat p) G * f ^ p) := by
          rw [← hqmul, hqG']
          ring
        have heq := congrArg (PowerSeries.coeff n) hexpand
        rw [map_add, PowerSeries.coeff_C_mul, hcorrection] at heq
        let corr : PLocalInteger p := PowerSeries.coeff n (G * F ^ p)
        have hcorrMap : PowerSeries.coeff n
              (PowerSeries.map (pLocalIntegerToRat p) G * Fq ^ p) =
            pLocalIntegerToRat p corr := by
          dsimp [corr, Fq]
          rw [← map_pow, ← map_mul, PowerSeries.coeff_map]
        rw [hcorrMap] at heq
        have hexpandCoeff : PowerSeries.coeff n
              (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero f) =
            PowerSeries.coeff n
              (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero Fq) := by
          rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
          split_ifs with hd
          · exact (hFq_lt (n / p)
              (Nat.div_lt_self hnpos (Fact.out : Nat.Prime p).one_lt)).symm
          · rfl
        rw [hexpandCoeff] at heq
        let A : ℚ⟦X⟧ := Fq + PowerSeries.monomial n (PowerSeries.coeff n f)
        have hAcoeff (i : ℕ) (hi : i ≤ n) :
            PowerSeries.coeff i A = PowerSeries.coeff i f := by
          by_cases hin : i = n
          · subst i
            simp [A, hFq_n]
          · have hil : i < n := lt_of_le_of_ne hi hin
            simp [A, PowerSeries.coeff_monomial, hin, hFq_lt i hil]
        have hfpn : PowerSeries.coeff n (f ^ p) =
            (p : ℚ) * PowerSeries.coeff n f + PowerSeries.coeff n (Fq ^ p) := by
          rw [coeff_pow_eq_of_coeff_eq_up_to (r := p)
            (fun i hi => (hAcoeff i hi).symm)]
          exact coeff_pow_add_monomial p Fq hFq0 hn (PowerSeries.coeff n f)
        rw [hfpn] at heq
        obtain ⟨b, hb⟩ := pLocal_frobeniusCoefficientDivisible p F n
        have hbq : PowerSeries.coeff n
              (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero Fq - Fq ^ p) =
            (p : ℚ) * pLocalIntegerToRat p b := by
          rw [map_sub] at hb
          have hb' := congrArg (pLocalIntegerToRat p) hb
          rw [map_sub, map_mul, map_natCast] at hb'
          dsimp [Fq]
          have hexpmap : PowerSeries.coeff n
                (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero
                  (PowerSeries.map (pLocalIntegerToRat p) F)) =
              pLocalIntegerToRat p (PowerSeries.coeff n
                (PowerSeries.expand p (Fact.out : Nat.Prime p).ne_zero F)) := by
            rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
            split_ifs <;> simp [PowerSeries.coeff_map]
          have hpowmap : PowerSeries.coeff n
                (PowerSeries.map (pLocalIntegerToRat p) F ^ p) =
              pLocalIntegerToRat p (PowerSeries.coeff n (F ^ p)) := by
            rw [← map_pow, PowerSeries.coeff_map]
          rw [map_sub, hexpmap, hpowmap]
          exact hb'
        rw [map_sub] at hbq
        have hcoeffLift : PowerSeries.coeff n f = pLocalIntegerToRat p (b - corr) := by
          rw [map_sub]
          have hpq : (0 : ℚ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
          apply mul_left_cancel₀ (ne_of_gt hpq)
          nlinarith [heq, hbq]
        exact (isPIntegral_iff_exists_pLocalInteger p (PowerSeries.coeff n f)).mpr
          ⟨b - corr, hcoeffLift.symm⟩
 theorem rat_padicValuation_le_one_of_padicValRat_nonneg
    {q : ℚ} (hq : 0 ≤ padicValRat p q) : Rat.padicValuation p q ≤ 1 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · change (if q = 0 then 0 else WithZero.exp (-padicValRat p q)) ≤ 1
    rw [if_neg hq0]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
theorem artinHasse_frobeniusQuotient_pDivisible :
    IsPDivisibleOffConstant p
      (PowerSeries.rescale (p : ℚ) (PowerSeries.exp ℚ)) := by
  constructor
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    simp
  · intro n hn
    let a : ℚ := (p : ℚ) ^ (n - 1) / (n.factorial : ℚ)
    refine ⟨a, ?_, ?_⟩
    · apply rat_padicValuation_le_one_of_padicValRat_nonneg p
      have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      have hfacq : (n.factorial : ℚ) ≠ 0 := by positivity
      have hfac := padicValNat_factorial_lt_of_ne_zero p hn
      have hfac' : padicValNat p n.factorial ≤ n - 1 := by omega
      dsimp [a]
      rw [padicValRat.div (pow_ne_zero _ hpq) hfacq, padicValRat.pow,
        padicValRat.self (Fact.out : Nat.Prime p).one_lt, mul_one,
        padicValRat.of_nat]
      omega
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      change (p : ℚ) ^ n * (1 / (n.factorial : ℚ)) = (p : ℚ) * a
      have hpow : (p : ℚ) ^ n = (p : ℚ) * (p : ℚ) ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
        rw [pow_succ, mul_comm]
      rw [hpow]
      dsimp [a]
      ring
theorem artinHasseExponential_isPIntegral :
    IsPIntegralPowerSeries p (artinHasseExponential p) := by
  apply dworkIntegralityCriterion p (artinHasseExponential_constantCoeff p)
  rw [artinHasse_frobeniusQuotient]
  exact artinHasse_frobeniusQuotient_pDivisible p
omit [Fact p.Prime] in
@[simp]
theorem artinHasseExponential_coeff_one :
    PowerSeries.coeff 1 (artinHasseExponential p) = -1 := by
  change PowerSeries.coeff 1 (formalExponential (artinHasseLog p)) = -1
  have h := congrArg (PowerSeries.coeff 0)
    (formalExponential_derivative (artinHasseLog_constantCoeff p))
  simpa [PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, formalExponential_constantCoeff,
    artinHasseLog_coeff] using h
end FiniteFields.Dwork
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
 theorem coefficientField_norm_ratCast_le_one
    (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    ‖(q : CoefficientField k p)‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff]
  rw [show (q : CoefficientField k p) =
      ((q : WithVal (coefficientValuation k p)) : CoefficientField k p) by
        exact (map_ratCast
          (UniformSpace.Completion.coeRingHom :
            WithVal (coefficientValuation k p) →+* CoefficientField k p) q).symm]
  rw [Valued.valuedCompletion_apply]
  change coefficientValuation k p (q : CoefficientFractionField k p) ≤ 1
  have hden : ¬p ∣ q.den := Rat.padicValuation_le_one_iff.mp hq
  have hdenk : (q.den : k) ≠ 0 := by
    intro hz
    exact hden ((CharP.cast_eq_zero_iff k p q.den).mp hz)
  have hdenUnit : IsUnit (q.den : CoefficientRing k p) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change WittVector.constantCoeff (q.den : CoefficientRing k p) ≠ 0
    simpa only [map_natCast] using hdenk
  rw [Rat.cast_def, map_div₀]
  have hnum : coefficientValuation k p
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
        (q.num : CoefficientRing k p)) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal
      (CoefficientRing k p)).valuation_le_one (K := CoefficientFractionField k p) _
  have hdenVal : coefficientValuation k p
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
        (q.den : CoefficientRing k p)) = 1 :=
    Valuation.Integers.one_of_isUnit' hdenUnit
      (fun x => (IsDiscreteValuationRing.maximalIdeal
        (CoefficientRing k p)).valuation_le_one (K := CoefficientFractionField k p) x)
  have hdenVal' : coefficientValuation k p
      (q.den : CoefficientFractionField k p) = 1 := by
    simpa only [map_natCast] using hdenVal
  have hnum' : coefficientValuation k p
      (q.num : CoefficientFractionField k p) ≤ 1 := by
    simpa only [map_intCast] using hnum
  rw [hdenVal', div_one]
  exact hnum'
theorem dworkCyclotomic_norm_ratCast_le_one
    (q : ℚ) (hq : Rat.padicValuation p q ≤ 1) :
    ‖(q : DworkCyclotomicField k p)‖ ≤ 1 := by
  rw [show (q : DworkCyclotomicField k p) =
      algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
        (q : CoefficientField k p) by simp,
    dworkCyclotomicField_norm_algebraMap]
  exact coefficientField_norm_ratCast_le_one k p q hq
def dworkArtinHasseExponential :
    (DworkCyclotomicField k p)⟦X⟧ :=
  PowerSeries.map (Rat.castHom (DworkCyclotomicField k p))
    (artinHasseExponential p)
theorem dworkArtinHasseExponential_coeff_norm_le_one (n : ℕ) :
    ‖PowerSeries.coeff n (dworkArtinHasseExponential k p)‖ ≤ 1 := by
  rw [dworkArtinHasseExponential, PowerSeries.coeff_map]
  change ‖(↑(PowerSeries.coeff n (artinHasseExponential p)) :
    DworkCyclotomicField k p)‖ ≤ 1
  exact dworkCyclotomic_norm_ratCast_le_one k p _
    (artinHasseExponential_isPIntegral p n)
theorem dworkArtinHasse_rescale_coeff_norm_le
    (r : DworkCyclotomicField k p) (n : ℕ) :
    ‖PowerSeries.coeff n
      (PowerSeries.rescale r (dworkArtinHasseExponential k p))‖ ≤ ‖r‖ ^ n := by
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  calc
    ‖r‖ ^ n * ‖PowerSeries.coeff n (dworkArtinHasseExponential k p)‖ ≤
        ‖r‖ ^ n * 1 :=
      mul_le_mul_of_nonneg_left
        (dworkArtinHasseExponential_coeff_norm_le_one k p n)
        (pow_nonneg (norm_nonneg r) n)
    _ = ‖r‖ ^ n := mul_one _
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter PowerSeries
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
 noncomputable instance dworkCyclotomicFieldNonarchimedeanRing :
    NonarchimedeanRing (DworkCyclotomicField k p) :=
  { (inferInstance : IsTopologicalRing (DworkCyclotomicField k p)) with
    is_nonarchimedean :=
      NonarchimedeanAddGroup.is_nonarchimedean }
def dworkPowerSeriesEval
    (f : (DworkCyclotomicField k p)⟦X⟧)
    (x : DworkCyclotomicField k p) : DworkCyclotomicField k p :=
  ∑' n : ℕ, PowerSeries.coeff n f * x ^ n
 theorem summable_dworkPowerSeriesEval_terms
    (f : (DworkCyclotomicField k p)⟦X⟧)
    (x : DworkCyclotomicField k p)
    (hcoeff : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1)
    (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ => PowerSeries.coeff n f * x ^ n) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one (norm_nonneg x) hx)
  intro n
  rw [norm_mul, norm_pow]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (norm_nonneg x) n)
theorem hasSum_dworkPowerSeriesEval
    (f : (DworkCyclotomicField k p)⟦X⟧)
    (x : DworkCyclotomicField k p)
    (hcoeff : ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1)
    (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff n f * x ^ n)
      (dworkPowerSeriesEval k p f x) :=
  (summable_dworkPowerSeriesEval_terms k p f x hcoeff hx).hasSum
def BoundedDworkPowerSeries :
    Subring (DworkCyclotomicField k p)⟦X⟧ where
  carrier := {f | ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1}
  zero_mem' := by
    intro n
    simp
  one_mem' := by
    intro n
    simp only [PowerSeries.coeff_one]
    split_ifs <;> simp
  add_mem' := by
    intro f g hf hg n
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
  neg_mem' := by
    intro f hf n
    simpa using hf n
  mul_mem' := by
    intro f g hf hg n
    rw [PowerSeries.coeff_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro ij hij
    rw [norm_mul]
    exact mul_le_one₀ (hf ij.1) (norm_nonneg _) (hg ij.2)
 theorem boundedDworkPowerSeries_coeff_norm_le_one
    (f : BoundedDworkPowerSeries k p) (n : ℕ) :
    ‖PowerSeries.coeff n (f : (DworkCyclotomicField k p)⟦X⟧)‖ ≤ 1 :=
  f.property n
 theorem boundedDworkPowerSeries_hasSum
    (f : BoundedDworkPowerSeries k p)
    (x : DworkCyclotomicField k p) (hx : ‖x‖ < 1) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff n
        (f : (DworkCyclotomicField k p)⟦X⟧) * x ^ n)
      (dworkPowerSeriesEval k p f x) :=
  hasSum_dworkPowerSeriesEval k p f x
    (boundedDworkPowerSeries_coeff_norm_le_one k p f) hx
theorem dworkPowerSeriesEval_zero
    (x : DworkCyclotomicField k p) :
    dworkPowerSeriesEval k p
      (0 : BoundedDworkPowerSeries k p) x = 0 := by
  simp [dworkPowerSeriesEval]
theorem dworkPowerSeriesEval_one
    (x : DworkCyclotomicField k p) :
    dworkPowerSeriesEval k p
      (1 : BoundedDworkPowerSeries k p) x = 1 := by
  simp [dworkPowerSeriesEval]
theorem dworkPowerSeriesEval_add
    (x : DworkCyclotomicField k p) (hx : ‖x‖ < 1)
    (f g : BoundedDworkPowerSeries k p) :
    dworkPowerSeriesEval k p (f + g) x =
      dworkPowerSeriesEval k p f x + dworkPowerSeriesEval k p g x := by
  calc
    dworkPowerSeriesEval k p (f + g) x =
        ∑' n : ℕ,
          (PowerSeries.coeff n
              (f : (DworkCyclotomicField k p)⟦X⟧) * x ^ n +
            PowerSeries.coeff n
              (g : (DworkCyclotomicField k p)⟦X⟧) * x ^ n) := by
      unfold dworkPowerSeriesEval
      apply tsum_congr
      intro n
      rw [map_add, add_mul]
    _ = dworkPowerSeriesEval k p f x + dworkPowerSeriesEval k p g x :=
      ((boundedDworkPowerSeries_hasSum k p f x hx).add
        (boundedDworkPowerSeries_hasSum k p g x hx)).tsum_eq
 theorem dworkPowerSeriesEval_mul_term
    (x : DworkCyclotomicField k p)
    (f g : BoundedDworkPowerSeries k p) (n : ℕ) :
    PowerSeries.coeff n
          ((f * g : BoundedDworkPowerSeries k p) :
            (DworkCyclotomicField k p)⟦X⟧) * x ^ n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff ij.1
            (f : (DworkCyclotomicField k p)⟦X⟧) * x ^ ij.1) *
          (PowerSeries.coeff ij.2
            (g : (DworkCyclotomicField k p)⟦X⟧) * x ^ ij.2) := by
  change PowerSeries.coeff n
      ((f : (DworkCyclotomicField k p)⟦X⟧) *
        (g : (DworkCyclotomicField k p)⟦X⟧)) * x ^ n = _
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij' : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hij', pow_add]
  ring
theorem dworkPowerSeriesEval_mul
    (x : DworkCyclotomicField k p) (hx : ‖x‖ < 1)
    (f g : BoundedDworkPowerSeries k p) :
    dworkPowerSeriesEval k p (f * g) x =
      dworkPowerSeriesEval k p f x * dworkPowerSeriesEval k p g x := by
  let ft : ℕ → DworkCyclotomicField k p := fun n =>
    PowerSeries.coeff n (f : (DworkCyclotomicField k p)⟦X⟧) * x ^ n
  let gt : ℕ → DworkCyclotomicField k p := fun n =>
    PowerSeries.coeff n (g : (DworkCyclotomicField k p)⟦X⟧) * x ^ n
  have hf : Summable ft := (boundedDworkPowerSeries_hasSum k p f x hx).summable
  have hg : Summable gt := (boundedDworkPowerSeries_hasSum k p g x hx).summable
  have hfg : Summable (fun ij : ℕ × ℕ => ft ij.1 * gt ij.2) :=
    hf.mul_of_nonarchimedean hg
  calc
    dworkPowerSeriesEval k p (f * g) x =
        ∑' n : ℕ, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ft ij.1 * gt ij.2 := by
          unfold dworkPowerSeriesEval
          apply tsum_congr
          exact dworkPowerSeriesEval_mul_term k p x f g
    _ = (∑' n, ft n) * ∑' n, gt n :=
      (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg).symm
    _ = dworkPowerSeriesEval k p f x * dworkPowerSeriesEval k p g x := rfl
def dworkPowerSeriesEvalRingHom
    (x : DworkCyclotomicField k p) (hx : ‖x‖ < 1) :
    BoundedDworkPowerSeries k p →+* DworkCyclotomicField k p where
  toFun f := dworkPowerSeriesEval k p f x
  map_zero' := dworkPowerSeriesEval_zero k p x
  map_one' := dworkPowerSeriesEval_one k p x
  map_add' := dworkPowerSeriesEval_add k p x hx
  map_mul' := dworkPowerSeriesEval_mul k p x hx
end FiniteFields.Dwork
end
end

section
noncomputable section
open Filter Function IsUltrametricDist Metric PowerSeries Set
open scoped NNReal Topology
namespace FiniteFields.Dwork
variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k]
def dworkArtinHasseEval (x : DworkCyclotomicField k p) :
    DworkCyclotomicField k p :=
  dworkPowerSeriesEval k p (dworkArtinHasseExponential k p) x
 def dworkArtinHasseTail (x : DworkCyclotomicField k p) :
    DworkCyclotomicField k p :=
  ∑' n : ℕ,
    PowerSeries.coeff (n + 2) (dworkArtinHasseExponential k p) * x ^ (n + 2)
 theorem dworkArtinHasse_terms_summable
    {x : DworkCyclotomicField k p} (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n) :=
  (hasSum_dworkPowerSeriesEval k p (dworkArtinHasseExponential k p) x
    (dworkArtinHasseExponential_coeff_norm_le_one k p) hx).summable
 theorem dworkArtinHasse_tail_summable
    {x : DworkCyclotomicField k p} (hx : ‖x‖ < 1) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff (n + 2) (dworkArtinHasseExponential k p) * x ^ (n + 2)) := by
  simpa only [Function.comp_def, Nat.add_comm] using
    (dworkArtinHasse_terms_summable k p hx).comp_injective (add_right_injective 2)
 theorem dworkArtinHasseEval_eq_one_sub_add_tail
    {x : DworkCyclotomicField k p} (hx : ‖x‖ < 1) :
    dworkArtinHasseEval k p x = 1 - x + dworkArtinHasseTail k p x := by
  let term : ℕ → DworkCyclotomicField k p := fun n =>
    PowerSeries.coeff n (dworkArtinHasseExponential k p) * x ^ n
  have hsum : Summable term := dworkArtinHasse_terms_summable k p hx
  have hsplit := hsum.sum_add_tsum_nat_add 2
  change (∑' n : ℕ, term n) = 1 - x + ∑' n : ℕ, term (n + 2)
  rw [← hsplit]
  norm_num [Finset.sum_range_succ, term, dworkArtinHasseExponential,
    PowerSeries.coeff_map]
  ring
 theorem dworkArtinHasseTail_norm_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : DworkCyclotomicField k p} (hx : ‖x‖ ≤ r) :
    ‖dworkArtinHasseTail k p x‖ ≤ r := by
  apply norm_tsum_le_of_forall_le_of_nonneg hr0
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖PowerSeries.coeff (n + 2) (dworkArtinHasseExponential k p)‖ * ‖x‖ ^ (n + 2) ≤
        1 * ‖x‖ ^ (n + 2) :=
      mul_le_mul_of_nonneg_right
        (dworkArtinHasseExponential_coeff_norm_le_one k p (n + 2))
        (pow_nonneg (norm_nonneg x) _)
    _ ≤ 1 * r ^ (n + 2) := by
      gcongr
    _ = r ^ (n + 2) := one_mul _
    _ ≤ r := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one hr0 hr1 (show 1 ≤ n + 2 by omega))
 theorem norm_pow_sub_pow_le_mul
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x y : DworkCyclotomicField k p} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r)
    {m : ℕ} (hm : 2 ≤ m) :
    ‖x ^ m - y ^ m‖ ≤ r * ‖x - y‖ := by
  rw [← (Commute.all x y).mul_geom_sum₂ m, norm_mul]
  have hrange : (Finset.range m).Nonempty :=
    ⟨0, Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_two hm)⟩
  have hgeom :
      ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ ≤ r := by
    apply norm_sum_le_of_forall_le_of_nonempty hrange
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, norm_pow]
    calc
      ‖x‖ ^ i * ‖y‖ ^ (m - 1 - i) ≤
          r ^ i * r ^ (m - 1 - i) := by
        gcongr
      _ = r ^ (m - 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ r := by
        simpa only [pow_one] using
          (pow_le_pow_of_le_one hr0 hr1 (show 1 ≤ m - 1 by omega))
  calc
    ‖x - y‖ * ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ ≤
        ‖x - y‖ * r := mul_le_mul_of_nonneg_left hgeom (norm_nonneg _)
    _ = r * ‖x - y‖ := mul_comm _ _
 theorem dworkArtinHasseTail_sub_norm_le
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {x y : DworkCyclotomicField k p} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖dworkArtinHasseTail k p x - dworkArtinHasseTail k p y‖ ≤
      r * ‖x - y‖ := by
  have hsx := dworkArtinHasse_tail_summable k p (hx.trans_lt hr1)
  have hsy := dworkArtinHasse_tail_summable k p (hy.trans_lt hr1)
  rw [dworkArtinHasseTail, dworkArtinHasseTail, ← hsx.tsum_sub hsy]
  apply norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hr0 (norm_nonneg _))
  intro n
  rw [← mul_sub, norm_mul]
  calc
    ‖PowerSeries.coeff (n + 2) (dworkArtinHasseExponential k p)‖ *
        ‖x ^ (n + 2) - y ^ (n + 2)‖ ≤
      1 * (r * ‖x - y‖) := by
        exact mul_le_mul
          (dworkArtinHasseExponential_coeff_norm_le_one k p (n + 2))
          (norm_pow_sub_pow_le_mul k p hr0 hr1.le hx hy (show 2 ≤ n + 2 by omega))
          (norm_nonneg _) zero_le_one
    _ = r * ‖x - y‖ := one_mul _
 def dworkArtinHasseInverseStep (x : DworkCyclotomicField k p) :
    DworkCyclotomicField k p :=
  -dworkRamificationParameter k p + dworkArtinHasseTail k p x
 def dworkArtinHasseParameterBall : Set (DworkCyclotomicField k p) :=
  Metric.closedBall 0 ‖dworkRamificationParameter k p‖
 theorem dworkArtinHasseParameterBall_complete :
    IsComplete (dworkArtinHasseParameterBall k p) := by
  exact Metric.isClosed_closedBall.isComplete
 theorem dworkArtinHasseInverseStep_mapsTo :
    MapsTo (dworkArtinHasseInverseStep k p)
      (dworkArtinHasseParameterBall k p)
      (dworkArtinHasseParameterBall k p) := by
  intro x hx
  have hx' : ‖x‖ ≤ ‖dworkRamificationParameter k p‖ := by
    simpa [dworkArtinHasseParameterBall] using hx
  have htail : ‖dworkArtinHasseTail k p x‖ ≤
      ‖dworkRamificationParameter k p‖ :=
    dworkArtinHasseTail_norm_le k p (norm_nonneg _)
      (dworkRamificationParameter_norm_lt_one k p).le hx'
  have hstep : ‖dworkArtinHasseInverseStep k p x‖ ≤
      ‖dworkRamificationParameter k p‖ := by
    refine (norm_add_le_max
      (-dworkRamificationParameter k p) (dworkArtinHasseTail k p x)).trans ?_
    simpa using max_le (le_refl ‖dworkRamificationParameter k p‖) htail
  simpa [dworkArtinHasseParameterBall] using hstep
 theorem dworkArtinHasseInverseStep_contracting :
    ContractingWith ‖dworkRamificationParameter k p‖₊
      ((dworkArtinHasseInverseStep_mapsTo k p).restrict
        (dworkArtinHasseInverseStep k p)
        (dworkArtinHasseParameterBall k p)
        (dworkArtinHasseParameterBall k p)) := by
  constructor
  · exact_mod_cast dworkRamificationParameter_norm_lt_one k p
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (dworkArtinHasseInverseStep k p x.1)
        (dworkArtinHasseInverseStep k p y.1) ≤
      (‖dworkRamificationParameter k p‖₊ : ℝ) * dist x.1 y.1
    rw [dist_eq_norm, dist_eq_norm]
    have hx := x.2
    change x.1 ∈ Metric.closedBall 0 ‖dworkRamificationParameter k p‖ at hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hy := y.2
    change y.1 ∈ Metric.closedBall 0 ‖dworkRamificationParameter k p‖ at hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    simpa only [coe_nnnorm, dworkArtinHasseInverseStep, add_sub_add_left_eq_sub] using
      (dworkArtinHasseTail_sub_norm_le k p (norm_nonneg _)
        (dworkRamificationParameter_norm_lt_one k p) hx hy)
 theorem dworkPrimitiveRoot_eq_one_add_ramification :
    dworkPrimitiveRoot k p = 1 + dworkRamificationParameter k p := by
  rw [dworkRamificationParameter]
  ring
 theorem dworkArtinHasseInverseStep_fixed_iff_eval
    {x : DworkCyclotomicField k p} (hx : ‖x‖ < 1) :
    IsFixedPt (dworkArtinHasseInverseStep k p) x ↔
      dworkArtinHasseEval k p x = dworkPrimitiveRoot k p := by
  rw [dworkArtinHasseEval_eq_one_sub_add_tail k p hx,
    dworkPrimitiveRoot_eq_one_add_ramification]
  constructor
  · intro h
    change -dworkRamificationParameter k p + dworkArtinHasseTail k p x = x at h
    linear_combination h
  · intro h
    change -dworkRamificationParameter k p + dworkArtinHasseTail k p x = x
    linear_combination h
theorem existsUnique_dworkArtinHasseParameter :
    ∃! eta : DworkCyclotomicField k p,
      ‖eta‖ ≤ ‖dworkRamificationParameter k p‖ ∧
      ‖eta‖ < 1 ∧
      dworkArtinHasseEval k p eta = dworkPrimitiveRoot k p := by
  let step := dworkArtinHasseInverseStep k p
  let ball := dworkArtinHasseParameterBall k p
  have hcomplete : IsComplete ball := dworkArtinHasseParameterBall_complete k p
  have hmaps : MapsTo step ball ball := dworkArtinHasseInverseStep_mapsTo k p
  have hcontract : ContractingWith ‖dworkRamificationParameter k p‖₊
      (hmaps.restrict step ball ball) := dworkArtinHasseInverseStep_contracting k p
  have hzero : (0 : DworkCyclotomicField k p) ∈ ball := by
    change (0 : DworkCyclotomicField k p) ∈
      Metric.closedBall 0 ‖dworkRamificationParameter k p‖
    rw [Metric.mem_closedBall, dist_self]
    exact norm_nonneg _
  have hfinite : edist (0 : DworkCyclotomicField k p) (step 0) ≠ ⊤ :=
    edist_ne_top _ _
  obtain ⟨eta, hetaBall, hetaFixed, _hetaTendsto, _hetaRate⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hzero hfinite
  have hetaNorm : ‖eta‖ ≤ ‖dworkRamificationParameter k p‖ := by
    change eta ∈ Metric.closedBall 0 ‖dworkRamificationParameter k p‖ at hetaBall
    rwa [Metric.mem_closedBall, dist_zero_right] at hetaBall
  have hetaLt : ‖eta‖ < 1 :=
    hetaNorm.trans_lt (dworkRamificationParameter_norm_lt_one k p)
  refine ⟨eta, ⟨hetaNorm, hetaLt,
    (dworkArtinHasseInverseStep_fixed_iff_eval k p hetaLt).mp hetaFixed⟩, ?_⟩
  intro y hy
  have hyBall : y ∈ ball := by
    change y ∈ Metric.closedBall 0 ‖dworkRamificationParameter k p‖
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.1
  have hyFixed : IsFixedPt step y :=
    (dworkArtinHasseInverseStep_fixed_iff_eval k p hy.2.1).mpr hy.2.2
  have hetaFixedSub : IsFixedPt (hmaps.restrict step ball ball) ⟨eta, hetaBall⟩ := by
    apply Subtype.ext
    exact hetaFixed
  have hyFixedSub : IsFixedPt (hmaps.restrict step ball ball) ⟨y, hyBall⟩ := by
    apply Subtype.ext
    exact hyFixed
  exact (congrArg Subtype.val
    (hcontract.fixedPoint_unique' hetaFixedSub hyFixedSub)).symm
def dworkArtinHasseParameter : DworkCyclotomicField k p :=
  (existsUnique_dworkArtinHasseParameter k p).choose
theorem dworkArtinHasseParameter_norm_lt_one :
    ‖dworkArtinHasseParameter k p‖ < 1 :=
  (existsUnique_dworkArtinHasseParameter k p).choose_spec.1.2.1
def dworkSplittingFunction : (DworkCyclotomicField k p)⟦X⟧ :=
  PowerSeries.rescale (dworkArtinHasseParameter k p)
    (dworkArtinHasseExponential k p)
theorem dworkSplittingFunction_coeff_norm_le (n : ℕ) :
    ‖PowerSeries.coeff n (dworkSplittingFunction k p)‖ ≤
      ‖dworkArtinHasseParameter k p‖ ^ n := by
  exact dworkArtinHasse_rescale_coeff_norm_le k p
    (dworkArtinHasseParameter k p) n
end FiniteFields.Dwork
end
end


