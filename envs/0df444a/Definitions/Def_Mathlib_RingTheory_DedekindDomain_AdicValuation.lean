-- Prove2me | Definitions.Def_Mathlib_RingTheory_DedekindDomain_AdicValuation
-- name    : Mathlib_RingTheory_DedekindDomain_AdicValuation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2205f8a8-326f-5012-91e9-d6e97fd7a2e7
-- title:
--   Adic valuation as ideal multiplicity; separable adic completions
-- statement:
--   Two supplements to Mathlib's theory of valuations attached to height-one primes of a Dedekind domain are made here, both in the namespace `IsDedekindDomain.HeightOneSpectrum`.
--
--   The first is an instance recording separability of adic completions. For a Dedekind domain $R$ with fraction field $K$ and a height-one prime $v$ of $R$, if $K$ is countable as a type then the completion $v.\mathrm{adicCompletion}\ K$ of $K$ at $v$ is a separable topological space: the countable set obtained as the image of $K$ under the canonical map into the completion is dense, by `denseRange_algebraMap`. Thus the topological space underlying the $v$-adic completion of a countable fraction field admits a countable dense subset.
--
--   The second is the lemma [`IsDedekindDomain.HeightOneSpectrum.intValuation_eq_coe_neg_multiplicity`](../def/DedekindDomain_AdicValuation_InlineSpecific.html#L26): for a Dedekind domain $A$, a height-one prime $v$ of $A$ with underlying prime ideal `v.asIdeal`, and a nonzero $a \in A$, the integral valuation $v.\mathrm{intValuation}\ a$ equals $\mathrm{WithZero.exp}\bigl(-m\bigr)$, where $m \in \mathbb{Z}$ is the multiplicity of `v.asIdeal` in the principal ideal $\langle a\rangle =$ `Ideal.span {a}`, that is, the largest $n$ with $v^{n} \mid \langle a\rangle$, coerced from $\mathbb{N}$ to $\mathbb{Z}$; here $\mathrm{WithZero.exp}$ is the embedding of $\mathbb{Z}$ into the multiplicative group with zero in which the valuation takes its values. The proof rewrites Mathlib's definition of `intValuation` for nonzero arguments, which is phrased through the count of `v.asIdeal` among the normalised factors of $\langle a\rangle$ in the monoid of associated ideals, and identifies that count with the multiplicity.
--
--   **Relation to Mathlib.** `intValuation`, `adicCompletion` and `multiplicity` are Mathlib notions; this module adds to Mathlib's namespace a reformulation of `intValuation` in terms of `multiplicity` (Mathlib's own definition proceeds via counts of normalised factors) together with a separability instance for adic completions of a countable fraction field.
--
--   **Where it is used.** These facts serve the handling of $v$-adic valuations and their completions in the number-theoretic parts of the development, where valuations of elements of a Dedekind domain must be computed ideal-theoretically and where topological properties of local fields are needed.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_DedekindDomain_AdicValuation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    ⟨_, Set.countable_range _, denseRange_algebraMap (K := K) (v := v)⟩

lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [intValuation_if_neg _ hnz, count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

end IsDedekindDomain.HeightOneSpectrum

end


