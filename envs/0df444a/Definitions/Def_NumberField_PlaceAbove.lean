-- Prove2me | Definitions.Def_NumberField_PlaceAbove
-- name    : NumberField_PlaceAbove
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/5d1d676c-e1c8-596f-8dc7-c890dd652253
-- title:
--   A chosen prime of OK​ above a prime of OE​
-- statement:
--   Throughout, $E$ is a number field, $K$ is a field equipped with an $E$-algebra structure, and primes are taken in the sense of Mathlib's `HeightOneSpectrum`, i.e. nonzero prime ideals of the ring of integers. The module supplies a once-and-for-all choice of a prime of $\mathcal{O}_K$ above a given prime of $\mathcal{O}_E$.
--
--   [`NumberField.PlaceAbove.exists_above`](../def/NumberField_PlaceAbove.html#L11) asserts that for every $v \in \operatorname{HeightOneSpectrum}(\mathcal{O}_E)$ there exists $w \in \operatorname{HeightOneSpectrum}(\mathcal{O}_K)$ whose underlying ideal contracts to that of $v$: the preimage of $w.\mathrm{asIdeal}$ under $\mathcal{O}_E \to \mathcal{O}_K$ equals $v.\mathrm{asIdeal}$. The proof first records that $\mathcal{O}_E \to \mathcal{O}_K$ is injective (it is the restriction of the field embedding $E \to K$ along the injections of the rings of integers into their fraction fields), then applies the going-up statement for integral extensions to the maximal ideal $v.\mathrm{asIdeal}$ to obtain a maximal ideal $W$ of $\mathcal{O}_K$ contracting to it, and checks $W \neq \bot$ because its contraction $v.\mathrm{asIdeal}$ is nonzero; the pair (prime, nonzero) is then repackaged as an element of the height-one spectrum.
--
--   [`NumberField.PlaceAbove.above E K v`](../def/NumberField_PlaceAbove.html#L27) is the resulting prime of $\mathcal{O}_K$, obtained as a (noncomputable) choice of a witness for that existence statement; it is therefore not canonical, but it is a fixed function of $E$, $K$ and $v$, so all later constructions indexed by primes of the base field refer to one and the same prime above. [`NumberField.PlaceAbove.comap_above`](../def/NumberField_PlaceAbove.html#L29) records its defining property, namely that the contraction of `(above E K v).asIdeal` along $\mathcal{O}_E \to \mathcal{O}_K$ is `v.asIdeal`; this is the only property of the choice that is available for use.
--
--   **Relation to Mathlib.** Mathlib provides the height-one spectrum of a Dedekind domain and the going-up theorem for integral extensions; what is added here is a named, fixed choice function $v \mapsto w$ between height-one spectra of rings of integers, together with its contraction property.
--
--   **Where it is used.** Later constructions attached to a finite place of the base field — completions, decomposition subgroups and the associated coinduced or idelic modules — are indexed by primes of $E$ while living over $K$, and they all use this single chosen prime above $v$, so that the objects so indexed match up on the nose rather than only up to the conjugation action of $\mathrm{Gal}(K/E)$ on the primes above $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_PlaceAbove.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]

theorem exists_above (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := fun x y hxy => by
    apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
    apply (algebraMap E K).injective
    have := congrArg (algebraMap (𝓞 K) K) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 E) E K] at this
  haveI := v.isMaximal
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hW0 : W ≠ ⊥ := by
    rintro rfl
    exact v.ne_bot (by rw [← hWv, Ideal.comap_bot_of_injective _ hinj])
  exact ⟨⟨W, hWmax.isPrime, hW0⟩, hWv⟩

noncomputable def above (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) := (exists_above E K v).choose

theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := (exists_above E K v).choose_spec

end NumberField.PlaceAbove


