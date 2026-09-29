-- Prove2me | Definitions.Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction
-- name    : Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/51ef999c-1d1e-5a7e-9c7a-4e6172772cff
-- title:
--   Smooth-over-a-field regular stalks reduced to standard smooth case
-- statement:
--   The module is organised around the project predicate `SmoothFieldFiberRegularStalksInput.{u}`, which is the proposition that for every field $k$ and every commutative $k$-algebra $A$ in universe $u$ with `Algebra.Smooth k A` (formally smooth and of finite presentation) and every prime $\mathfrak p \subseteq A$, the local ring `Localization.AtPrime p` is a regular local ring. The main result, [`kmf2_fiber_input_iff_standardSmooth_case`](../def/Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.html#L57), shows this proposition to be equivalent to its restriction to standard smooth algebras: for all $k$ and $B$ in universe $u$ with `Algebra.IsStandardSmooth k B` and all primes $\mathfrak q \subseteq B$, the ring $B_{\mathfrak q}$ is regular local. One direction is immediate from the implication standard smooth $\Rightarrow$ smooth; the other, [`kmf2_fiber_input_of_standardSmooth_case`](../def/Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.html#L17), passes for a given smooth $A$ and prime $\mathfrak p$ to an element $f \notin \mathfrak p$ with $A_f$ standard smooth over $k$, notes that $\mathfrak p A_f$ is prime with contraction $\mathfrak p$, and identifies $A_{\mathfrak p}$ with the localisation of $A_f$ at that prime. A helper, [`kmf2_fiber_isLocalization_primeCompl_congr`](../def/Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.html#L10), transports an `IsLocalization` instance for $\mathfrak I^{c}$ along an equality $I = J$ of primes.
--
--   The remaining declarations are unconditional instances of the conclusion and two negative checks. Localisations at all primes of a principal ideal domain are regular local; consequently $k[X]$ is a regular ring, its localisations at primes are regular local, and $k[X]$ is smooth over $k$ (recorded also as a conjunction). For a reduced Noetherian ring and a minimal prime, the localisation is regular local, because it is a reduced Artinian local ring, hence a field. Finally, the statement with the smoothness hypothesis deleted is false, witnessed by the dual numbers over $\mathbb Q$; and from the standard smooth case at `Type` level it follows that $\mathbb Q[\varepsilon]$ is not standard smooth over $\mathbb Q$.
--
--   **Relation to Mathlib.** [`SmoothFieldFiberRegularStalksInput`](../def/Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.html#L7) is the project's own packaging, as a single proposition, of the assertion that algebras smooth over a field have regular local rings at all primes; the predicates `Algebra.Smooth`, `Algebra.IsStandardSmooth`, `IsRegularLocalRing`, `IsRegularRing` and the localisation machinery, including `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`, are Mathlib's.
--
--   **Where it is used.** These results belong to the commutative-algebra layer on smoothness and regularity, isolating the standard smooth case as the only thing that has to be proved in order to know that algebras smooth over a field have regular local rings — the fibrewise half of the statement that smooth morphisms have regular fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

universe u

theorem kmf2_fiber_isLocalization_primeCompl_congr {A : Type*} [CommRing A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization I.primeCompl S] :
    IsLocalization J.primeCompl S := by
  subst h
  exact ‹IsLocalization I.primeCompl S›

theorem kmf2_fiber_input_of_standardSmooth_case
    (hss : ∀ (k B : Type u) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q)) :
    SmoothFieldFiberRegularStalksInput.{u} := by
  intro k A _ _ _ hsm p hp
  haveI : Algebra.Smooth k A := hsm

  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k p

  have hdisj : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  haveI hq : (p.map (algebraMap A (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p hp hdisj
  have hcomap : (p.map (algebraMap A (Localization.Away f))).comap
      (algebraMap A (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdisj

  haveI : IsRegularLocalRing
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f)))) :=
    hss k (Localization.Away f) hstd (p.map (algebraMap A (Localization.Away f)))

  haveI : IsLocalization p.primeCompl
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f)))) :=
    kmf2_fiber_isLocalization_primeCompl_congr hcomap _
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime p)
      (Localization.AtPrime (p.map (algebraMap A (Localization.Away f))))).symm.toRingEquiv)

theorem kmf2_fiber_standardSmooth_case_of_input
    (hinput : SmoothFieldFiberRegularStalksInput.{u})
    (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (hstd : Algebra.IsStandardSmooth k B) (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hstd
  exact hinput k B inferInstance q

theorem kmf2_fiber_input_iff_standardSmooth_case :
    SmoothFieldFiberRegularStalksInput.{u} ↔
      ∀ (k B : Type u) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q) :=
  ⟨fun h k B _ _ _ hstd q _ => kmf2_fiber_standardSmooth_case_of_input h k B hstd q,
   kmf2_fiber_input_of_standardSmooth_case⟩

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing
    (A : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : IsDedekindDomain A := inferInstance
  haveI : IsRegularRing A := inferInstance
  exact IsRegularRing.isRegularLocalRing_localization p

theorem kmf2_fiber_isRegularRing_polynomial (k : Type*) [Field k] :
    IsRegularRing (Polynomial k) := by
  haveI : IsDedekindDomain (Polynomial k) := inferInstance
  infer_instance

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial
    (k : Type*) [Field k] (p : Ideal (Polynomial k)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing
    (Polynomial k) p

theorem kmf2_fiber_sat_smooth_polynomial (k : Type*) [Field k] :
    Algebra.Smooth k (Polynomial k) :=
  { formallySmooth := inferInstance, finitePresentation := inferInstance }

theorem kmf2_fiber_gate_input_clause_polynomial (k : Type*) [Field k] :
    Algebra.Smooth k (Polynomial k) ∧
      ∀ (p : Ideal (Polynomial k)) [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p) := by
  refine ⟨kmf2_fiber_sat_smooth_polynomial k, ?_⟩
  intro p hp
  exact kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial k p

theorem kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isReduced_of_mem_minimalPrimes
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : IsNoetherianRing (Localization.AtPrime p) := inferInstance
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
  haveI : IsArtinianRing (Localization.AtPrime p) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  haveI : IsReduced (Localization.AtPrime p) := inferInstance
  exact SmoothFieldFiberRegularStalks.isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem kmf2_fiber_falsif_not_standardSmooth_case_dropping_standardSmooth :
    ¬ (∀ (k B : Type) [Field k] [CommRing B] [Algebra k B] (q : Ideal B) [q.IsPrime],
        IsRegularLocalRing (Localization.AtPrime q)) :=
  SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth

theorem kmf2_fiber_not_isStandardSmooth_dualNumber_of_standardSmooth_case
    (hss : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
        Algebra.IsStandardSmooth k B → ∀ (q : Ideal B) [q.IsPrime],
          IsRegularLocalRing (Localization.AtPrime q)) :
    ¬ Algebra.IsStandardSmooth ℚ (DualNumber ℚ) := fun h =>
  SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber ℚ
    (hss ℚ (DualNumber ℚ) h (IsLocalRing.maximalIdeal (DualNumber ℚ)))

/--
info: 'kmf2_fiber_isLocalization_primeCompl_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_isLocalization_primeCompl_congr

/--
info: 'kmf2_fiber_input_of_standardSmooth_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_input_of_standardSmooth_case

/--
info: 'kmf2_fiber_standardSmooth_case_of_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_standardSmooth_case_of_input

/--
info: 'kmf2_fiber_input_iff_standardSmooth_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_input_iff_standardSmooth_case

/--
info: 'kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isPrincipalIdealRing

/--
info: 'kmf2_fiber_isRegularRing_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_isRegularRing_polynomial

/--
info: 'kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_isRegularLocalRing_localization_atPrime_polynomial

/--
info: 'kmf2_fiber_sat_smooth_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_sat_smooth_polynomial

/--
info: 'kmf2_fiber_gate_input_clause_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_gate_input_clause_polynomial

/--
info: 'kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isReduced_of_mem_minimalPrimes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_isRegularLocalRing_localization_atPrime_of_isReduced_of_mem_minimalPrimes

/--
info: 'kmf2_fiber_falsif_not_standardSmooth_case_dropping_standardSmooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_falsif_not_standardSmooth_case_dropping_standardSmooth

/--
info: 'kmf2_fiber_not_isStandardSmooth_dualNumber_of_standardSmooth_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmf2_fiber_not_isStandardSmooth_dualNumber_of_standardSmooth_case


