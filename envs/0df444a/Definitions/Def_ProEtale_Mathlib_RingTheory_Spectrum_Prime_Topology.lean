-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Topology
-- name    : ProEtale_Mathlib_RingTheory_Spectrum_Prime_Topology
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:45.608321+00:00
-- url     : https://prove2.me/theorems/06593182-ac33-4ac1-bd1d-b3b8dc952bff
-- title:
--   The map from the disjoint union of spectra to the spectrum of a product, and spectrality of maps of prime spectra
-- statement:
--   For a family of commutative semirings $(R_i)_{i \in I}$, consider the canonical map
--   $$ \textstyle\coprod_i \operatorname{Spec} R_i \longrightarrow \operatorname{Spec}\big(\prod_i R_i\big), \qquad (i, \mathfrak p) \mapsto \pi_i^{-1}(\mathfrak p), $$
--   where $\pi_i$ is the $i$-th projection.
--
--   Principal results:
--   1. This map is continuous (for the disjoint union topology).
--   2. Its factors are pairwise incomparable: if the images of $(i,\mathfrak p)$ and $(j, \mathfrak q)$ satisfy $\pi_i^{-1}(\mathfrak p) \subseteq \pi_j^{-1}(\mathfrak q)$, then $i = j$.
--   3. For every ring homomorphism $f\colon R \to S$ of commutative semirings, the induced map $\operatorname{Spec} S \to \operatorname{Spec} R$ is a spectral map (continuous, with preimages of quasi-compact opens quasi-compact).
--
--   **Formalization Note** The declarations are `PrimeSpectrum.continuous_sigmaToPi`, `PrimeSpectrum.sigmaToPi_fst_eq_of_le` (the order on `PrimeSpectrum` is inclusion of prime ideals) and `PrimeSpectrum.isSpectralMap_comap`; the map is Mathlib's `PrimeSpectrum.sigmaToPi`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Spectrum/Prime/Topology.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Spectral.Hom

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- end of file
theorem PrimeSpectrum.continuous_sigmaToPi {ι : Type*} (R : ι → Type*)
    [(i : ι) → CommSemiring (R i)] :
    Continuous (PrimeSpectrum.sigmaToPi R) :=
  continuous_sigma fun _ ↦ continuous_comap (Pi.evalRingHom R _)

/-- The factors of `Spec (∀ i, R i)` are pairwise incomparable under specialization: if the
images under `PrimeSpectrum.sigmaToPi` of two points are comparable, they lie over the same
factor. -/
theorem PrimeSpectrum.sigmaToPi_fst_eq_of_le {ι : Type*} {R : ι → Type*}
    [∀ i, CommSemiring (R i)] {x y : Σ i, PrimeSpectrum (R i)}
    (h : PrimeSpectrum.sigmaToPi R x ≤ PrimeSpectrum.sigmaToPi R y) :
    x.1 = y.1 := by
  classical
  obtain ⟨i, p⟩ := x
  obtain ⟨j, q⟩ := y
  simp only [PrimeSpectrum.sigmaToPi_apply] at h
  by_contra hne
  have hmem : (Pi.single j 1 : ∀ k, R k) ∈
      (PrimeSpectrum.comap (Pi.evalRingHom R i) p).asIdeal := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    simp [Pi.single_eq_of_ne hne]
  have h1 : (1 : R j) ∈ q.asIdeal := by
    have h2 := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h hmem
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h2
    simpa using h2
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem PrimeSpectrum.isSpectralMap_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : IsSpectralMap (PrimeSpectrum.comap f) where
  toContinuous := PrimeSpectrum.continuous_comap f
  isCompact_preimage_of_isOpen s hs hc := by
    obtain ⟨I, hI_fg, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hc, hs⟩
    rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    refine (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hI_fg.map f, ?_⟩).1
    rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_eq, ← Ideal.span_eq I, Ideal.map_span,
      PrimeSpectrum.zeroLocus_span, Ideal.span_eq]


