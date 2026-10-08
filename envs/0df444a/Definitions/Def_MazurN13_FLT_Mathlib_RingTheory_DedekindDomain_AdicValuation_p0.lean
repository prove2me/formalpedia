-- Prove2me | Definitions.Def_MazurN13_FLT_Mathlib_RingTheory_DedekindDomain_AdicValuation_p0
-- name    : MazurN13_FLT_Mathlib_RingTheory_DedekindDomain_AdicValuation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:10:51.041703+00:00
-- url     : https://prove2.me/theorems/1ba7003b-d31c-42a3-9d4b-f93fc1257883
-- title:
--   FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
Original leading source comments and nonproject imports are retained below. -/
/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option autoImplicit false




/-!
# Adic Valuation

Material destined for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

-- TODO upstream
open IsDedekindDomain

instance instSeparableSpaceAdicCompletionOfCountable_fLT {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense := by
    have : Countable (WithVal (valuation K v)) :=
      Countable.of_equiv _ (WithVal.equiv (HeightOneSpectrum.valuation K v)).symm.toEquiv
    let f : WithVal (v.valuation K) → v.adicCompletion K :=
      adicCompletion.ofCompletion ∘ UniformSpace.Completion.coe'
    refine ⟨Set.range f, Set.countable_range f, ?_⟩
    change DenseRange f
    dsimp [f]
    exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
      UniformSpace.Completion.denseRange_coe
      (adicCompletion.continuous_ofCompletion K v)

lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

end IsDedekindDomain.HeightOneSpectrum


