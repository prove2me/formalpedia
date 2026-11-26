-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_GoingDown
-- name    : ProEtale_Mathlib_RingTheory_Ideal_GoingDown
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:13.879166+00:00
-- url     : https://prove2.me/theorems/7993d929-586a-4994-beea-827578fdd816
-- title:
--   Going-down maps hitting all closed points are surjective on spectra
-- statement:
--   Let $R \to S$ be a homomorphism of commutative rings satisfying going down. Suppose that every closed point of $\operatorname{Spec} R$, i.e. every maximal ideal of $R$, lies in the image of $\operatorname{Spec} S \to \operatorname{Spec} R$. Then
--   $$\operatorname{Spec} S \to \operatorname{Spec} R \text{ is surjective.}$$
--   Indeed, every prime is contained in a maximal ideal, and going down lifts the inclusion.
--
--   This criterion is used to show that flat maps (which satisfy going down) are faithfully flat once they hit all maximal ideals.
--
--   **Formalization Note** The Lean name is `Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage`, with hypothesis `[Algebra.HasGoingDown R S]` and an explicit hypothesis `closedPoints (PrimeSpectrum R) ⊆ Set.range (PrimeSpectrum.comap (algebraMap R S))`. The conclusion is `Function.Surjective (PrimeSpectrum.comap (algebraMap R S))`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Topology.JacobsonSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- after `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
theorem Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (h : closedPoints (PrimeSpectrum R) ⊆ Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  rintro ⟨p, hp⟩
  obtain ⟨m, hm, hle⟩  := Ideal.exists_le_maximal _ hp.ne_top
  have : ⟨m, hm.isPrime⟩ ∈ closedPoints (PrimeSpectrum R) := by
    rwa [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  obtain ⟨⟨n, _⟩, hn⟩ := h this
  have : n.LiesOver m := ⟨PrimeSpectrum.ext_iff.mp hn.symm⟩
  obtain ⟨q, _, hq, hpq⟩ := Ideal.exists_ideal_le_liesOver_of_le n hle
  use ⟨q, hq⟩, PrimeSpectrum.ext hpq.over.symm


