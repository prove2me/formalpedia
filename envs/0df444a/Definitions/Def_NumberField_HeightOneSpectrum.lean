-- Prove2me | Definitions.Def_NumberField_HeightOneSpectrum
-- name    : NumberField_HeightOneSpectrum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/db0134d4-371e-59cd-ad82-dd3eab2e2a04
-- title:
--   Countability of height-one spectra of rings of integers
-- statement:
--   This module records two instances, both of the form `Countable (HeightOneSpectrum (𝓞 ·))`, for the type of height-one primes (the nonzero prime ideals) of a ring of integers. Standing context: $K$ is a number field, so in particular its ring of integers $\mathcal{O}_K$ is a Dedekind domain with $K$ as fraction field.
--
--   The first instance asserts that `HeightOneSpectrum (𝓞 ℚ)` is countable; this is obtained by transport along the bijection `Rat.HeightOneSpectrum.primesEquiv` between the nonzero primes of the ring of integers of $\mathbb{Q}$ and the rational primes, a countable type.
--
--   The second instance asserts that `HeightOneSpectrum (𝓞 K)` is countable for every number field $K$. The mathematical content is that the map $w \mapsto w\ \text{under}\ \mathcal{O}_{\mathbb{Q}}$, sending a height-one prime of $\mathcal{O}_K$ to the height-one prime of $\mathcal{O}_{\mathbb{Q}}$ lying under it, has finite — hence countable — fibres: for a singleton $\{y\}$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$ its preimage is finite by `preimage_comap_finite`, applied with $A = \mathcal{O}_{\mathbb{Q}}$, $K = \mathbb{Q}$, $L = K$, $B = \mathcal{O}_K$; that lemma in turn rests on the finiteness of the set of primes of $B$ extending a given prime of $A$. Since a type admitting a map to a countable type with countable point-preimages is countable, the countability of `HeightOneSpectrum (𝓞 ℚ)` propagates to $\mathcal{O}_K$.
--
--   **Relation to Mathlib.** The bijection `Rat.HeightOneSpectrum.primesEquiv` between the height-one primes of the ring of integers of $\mathbb{Q}$ and the rational primes is Mathlib's; the finiteness of the fibres of `under` comes from the project's `preimage_comap_finite`. What is added here are the two `Countable` instances themselves, so that countability of the set of finite places of a number field is available to instance search.
--
--   **Where it is used.** The instances make countability of the set of finite places of a number field available automatically, as needed wherever constructions over a number field are indexed by its height-one primes, for instance in the treatment of finite adeles and restricted products.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/NumberField/HeightOneSpectrum.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_HeightOneSpectrum.lean

import Mathlib
import Definitions.Def_DedekindDomain_IntegralClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _
  Rat.HeightOneSpectrum.primesEquiv.symm

instance : Countable (HeightOneSpectrum (𝓞 K)) :=
  Set.Countable.of_preimage_singleton <| fun y ↦
  ((preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (by simp)).countable


