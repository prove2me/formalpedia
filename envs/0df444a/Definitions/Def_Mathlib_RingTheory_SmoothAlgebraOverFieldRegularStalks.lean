-- Prove2me | Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks
-- name    : Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/bca85cdd-1438-52b4-b943-c89943a77d08
-- title:
--   Regular stalks of smooth algebras over a field: hypothesis and cases
-- statement:
--   The single definition of the module is the Prop-valued statement [`SmoothFieldFiberRegularStalksInput`](../def/Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.html#L7), quantified over a universe $u$: for every field $k$ and every commutative $k$-algebra $A$, both in universe $u$, if `Algebra.Smooth k A` holds then for every prime ideal $\mathfrak p$ of $A$ the localisation `Localization.AtPrime` $\mathfrak p$ is a regular local ring. It is thus a named placeholder for the fibre half of the standard regularity criterion for smooth algebras over a field, stated as a hypothesis that other declarations may take as input; `smoothFieldFiberRegularStalksInput_iff` records that it is literally this quantified assertion, and `isRegularRing_of_smooth_of_input` deduces from it that a smooth $k$-algebra $A$ is a regular ring (the Noetherian hypothesis in `IsRegularRing` coming from finite type over $k$).
--
--   The remaining declarations prove special cases and a limiting example unconditionally. A field is a regular local ring; if $A$ is Artinian and reduced then each `Localization.AtPrime` $\mathfrak p$ is a field, hence regular, and $A$ is a regular ring. If $A$ is a formally unramified, essentially finite type $k$-algebra, each localisation at a prime is again formally unramified over $k$, hence finite and free, hence Artinian and reduced, hence a field; this yields the étale case and, with Noetherianity from finite type, that an étale $k$-algebra is a regular ring. Finally, for the dual numbers $K[\varepsilon]$ over a field $K$ it is shown that $\varepsilon \neq 0$, that the nilradical is $(\varepsilon)$, that the Krull dimension is $0$ while the maximal ideal needs one generator, so $K[\varepsilon]$ is not regular local; a regular local ring of Krull dimension at most $0$ is a field, and the localisation of $K[\varepsilon]$ at its maximal ideal is not regular. Consequently the quantified statement with the smoothness hypothesis deleted is false, witnessed by $\mathbb{Q}[\varepsilon]$.
--
--   **Relation to Mathlib.** `IsRegularLocalRing`, `IsRegularRing`, `Algebra.Smooth`, `Algebra.Etale`, `Algebra.FormallyUnramified`, `Algebra.EssFiniteType` and `DualNumber` are Mathlib notions; the module adds only the Prop [`SmoothFieldFiberRegularStalksInput`](../def/Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.html#L7), which packages as a hypothesis the assertion that smooth algebras over a field have regular local rings at all primes.
--
--   **Where it is used.** The module supplies, for one further module of the development, the commutative-algebra fact that local rings of a smooth (in the proved cases, étale, or Artinian reduced) algebra over a field are regular, together with the named hypothesis under which the smooth case may be invoked.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open IsLocalRing

def SmoothFieldFiberRegularStalksInput : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
      IsRegularLocalRing (Localization.AtPrime p)

namespace SmoothFieldFiberRegularStalks

theorem isRegularLocalRing_of_isField (R : Type*) [CommRing R] (hf : IsField R) :
    IsRegularLocalRing R := by
  letI := hf.toField
  infer_instance

theorem isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem isRegularRing_of_isArtinianRing_of_isReduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] :
    IsRegularRing A := by
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced A p

theorem isRegularLocalRing_localization_atPrime_of_formallyUnramified
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FormallyUnramified k A] [Algebra.EssFiniteType k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := Localization.AtPrime p) p.primeCompl
  haveI : Algebra.FormallyUnramified k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.comp k A (Localization.AtPrime p)
  haveI : Module.Finite k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.finite_of_free k (Localization.AtPrime p)
  haveI : IsArtinianRing (Localization.AtPrime p) :=
    IsArtinianRing.of_finite k (Localization.AtPrime p)
  haveI : IsReduced (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.isReduced_of_field k (Localization.AtPrime p)
  exact isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

theorem isRegularLocalRing_localization_atPrime_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_localization_atPrime_of_formallyUnramified k A p

theorem isRegularRing_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A] :
    IsRegularRing A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_localization_atPrime_of_etale k A p

theorem smoothFieldFiberRegularStalksInput_iff :
    SmoothFieldFiberRegularStalksInput.{u} ↔
      ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
        Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
          IsRegularLocalRing (Localization.AtPrime p) :=
  Iff.rfl

theorem isRegularRing_of_smooth_of_input
    (hinput : SmoothFieldFiberRegularStalksInput.{u})
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsRegularRing A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact hinput k A ‹Algebra.Smooth k A› p

theorem eps_ne_zero (K : Type*) [Field K] : (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro heq
  have h1 := congrArg TrivSqZeroExt.snd heq
  simp at h1

theorem nilradical_dualNumber_eq_span_eps (K : Type*) [Field K] :
    nilradical (DualNumber K) = Ideal.span {(DualNumber.eps : DualNumber K)} := by
  rcases DualNumber.ideal_trichotomy (nilradical (DualNumber K)) with h0 | h1 | h2
  · exfalso
    have hin : (DualNumber.eps : DualNumber K) ∈ nilradical (DualNumber K) :=
      mem_nilradical.mpr DualNumber.isNilpotent_eps
    rw [h0] at hin
    exact eps_ne_zero K (by simpa using hin)
  · exact h1
  · exfalso
    have hone : IsNilpotent (1 : DualNumber K) :=
      mem_nilradical.mp (h2 ▸ Submodule.mem_top)
    obtain ⟨n, hn⟩ := hone
    rw [one_pow] at hn
    exact one_ne_zero hn

theorem ringKrullDim_dualNumber_eq_zero (K : Type*) [Field K] :
    ringKrullDim (DualNumber K) = 0 := by
  haveI : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  haveI : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

theorem spanFinrank_maximalIdeal_dualNumber_eq_one (K : Type*) [Field K] :
    (maximalIdeal (DualNumber K)).spanFinrank = 1 := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, ← Ideal.submodule_span_eq]
  exact Submodule.spanFinrank_singleton (eps_ne_zero K)

theorem not_isRegularLocalRing_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (DualNumber K) := by
  intro h
  have hspan := h.spanFinrank_maximalIdeal
  rw [ringKrullDim_dualNumber_eq_zero K, spanFinrank_maximalIdeal_dualNumber_eq_one K]
    at hspan
  have h10 : (1 : ℕ) = 0 := by exact_mod_cast hspan
  exact one_ne_zero h10

theorem isField_of_isRegularLocalRing_of_krullDimLE_zero
    (R : Type*) [CommRing R] [Ring.KrullDimLE 0 R] [IsRegularLocalRing R] :
    IsField R := by
  have hspan := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp ‹Ring.KrullDimLE 0 R›] at hspan
  have h0 : (maximalIdeal R).spanFinrank = 0 := by exact_mod_cast hspan
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    ((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0)

theorem not_isRegularLocalRing_localization_atPrime_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (Localization.AtPrime (maximalIdeal (DualNumber K))) := by
  intro h

  haveI : IsNoetherianRing (DualNumber K) := PrincipalIdealRing.isNoetherianRing
  haveI : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  haveI : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  haveI : IsArtinianRing (DualNumber K) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

  have hf : IsField (Localization.AtPrime (maximalIdeal (DualNumber K))) :=
    isField_of_isRegularLocalRing_of_krullDimLE_zero
      (Localization.AtPrime (maximalIdeal (DualNumber K)))
  letI := hf.toField
  have hz : algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps = 0 :=
    (DualNumber.isNilpotent_eps.map (algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))))).eq_zero

  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff
    (maximalIdeal (DualNumber K)).primeCompl
    (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps).mp hz
  have hu : IsUnit m := by
    by_contra hnu
    exact hm ((IsLocalRing.mem_maximalIdeal m).mpr hnu)
  exact eps_ne_zero K (hu.mul_right_eq_zero.mp hm')

theorem not_forall_regular_stalks_without_smooth :
    ¬ (∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (p : Ideal A) [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p)) := by
  intro hclaim
  exact not_isRegularLocalRing_localization_atPrime_dualNumber ℚ
    (hclaim ℚ (DualNumber ℚ) (maximalIdeal (DualNumber ℚ)))

end SmoothFieldFiberRegularStalks

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified

/--
info: 'SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_etale

/--
info: 'SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber

/--
info: 'SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth


