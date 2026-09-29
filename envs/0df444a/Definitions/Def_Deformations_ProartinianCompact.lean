-- Prove2me | Definitions.Def_Deformations_ProartinianCompact
-- name    : Deformations_ProartinianCompact
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3b73c621-05ab-5bd0-917b-2b4efbfad1a0
-- title:
--   Compactness of pro-Artinian rings with finite residue field
-- statement:
--   Three auxiliary results and two instances, all concerning finiteness and compactness under the hypothesis that the residue field is finite.
--
--   The first lemma, [`IsArtinianRing.finite_of_finite_residueField`](../thm.html#IsArtinianRing.finite_of_finite_residueField), states that a commutative Artinian local ring $R$ whose residue field is finite is itself a finite ring; the argument uses nilpotence of the Jacobson radical, which for a local ring is the maximal ideal, together with finiteness of $R/\mathfrak m^n$ for a Noetherian ring with finite residue field.
--
--   The remaining two results are stated for a commutative topological ring $R$ that is local and satisfies the project's class [`IsProartinian`](../def/Deformations_IsProartinian.html#L185) — linearly topologized by ideals, $T_0$, complete for the right uniformity of its additive group, and such that $R/I$ is Artinian for every open ideal $I$ — with finite residue field. Under these hypotheses [`IsProartinian.finite_quotient_of_isOpen`](../thm.html#IsProartinian.finite_quotient_of_isOpen) asserts that $R/I$ is finite for every open ideal $I$ (the case $I=\top$ being trivial, and otherwise $R/I$ is Artinian local with residue field a quotient of that of $R$), and [`IsProartinian.compactSpace_of_finite_residueField`](../def/Deformations_ProartinianCompact.html#L47) asserts that $R$ is a compact space, obtained from completeness together with total boundedness: each neighbourhood of $0$ contains an open ideal of finite index, and finitely many coset representatives suffice.
--
--   The two instances transport this to the category $\mathcal C_{\mathcal O}$ of local pro-Artinian $\mathcal O$-algebras: for $\mathcal O$ a commutative local ring with finite residue field, every object $A$ of `ProartinianCat 𝓞` has finite residue field, because $k(\mathcal O)\to k(A)$ is bijective for such $A$, and consequently $A$ is compact.
--
--   **Relation to Mathlib.** Mathlib supplies the Artinian, Noetherian and linear-topology ingredients (`IsArtinianRing.isNilpotent_jacobson_bot`, `Ideal.finite_quotient_pow`, `IsLinearTopology.hasBasis_open_ideal`); the class [`IsProartinian`](../def/Deformations_IsProartinian.html#L185) and the category `ProartinianCat` are the project's own, and the `CompactSpace` instance for its objects is registered here.
--
--   **Where it is used.** Compactness of the objects of $\mathcal C_{\mathcal O}$ is part of the basic infrastructure for the deformation theory of Galois representations used in the proof: it is what makes the pro-Artinian framework behave profinitely, so that closed subalgebras and limits of such objects remain in the category.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (portions (≈16%; about six lines — the proof that a proper open ideal of a pro-Artinian ring has Artinian local quotient — match FLT/Deformations/IsProartinian.lean): `FLT/Deformations/IsProartinian.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_ProartinianCompact.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing Filter Topology Set Pointwise

private lemma IsArtinianRing.finite_of_finite_residueField (R : Type*) [CommRing R] [IsArtinianRing R]
    [IsLocalRing R] [Finite (ResidueField R)] : Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  have h1 : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  have h2 : Finite (R ⧸ maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

namespace IsProartinian

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLocalRing R] [IsProartinian R] [Finite (ResidueField R)]

private lemma finite_quotient_of_isOpen (I : Ideal R) (hI : IsOpen (X := R) I) :
    Finite (R ⧸ I) := by
  by_cases hI' : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI'
    exact Finite.of_subsingleton

  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective

  have hsurj : Function.Surjective (ResidueField.map (Ideal.Quotient.mk I)) := by
    have hcomp : Function.Surjective
        (ResidueField.map (Ideal.Quotient.mk I) ∘ residue R) := by
      rw [show ResidueField.map (Ideal.Quotient.mk I) ∘ residue R
            = residue (R ⧸ I) ∘ Ideal.Quotient.mk I from
          funext fun r ↦ ResidueField.map_residue _ r]
      exact (residue_surjective).comp Ideal.Quotient.mk_surjective
    exact hcomp.of_comp
  have : Finite (ResidueField (R ⧸ I)) := .of_surjective _ hsurj
  exact IsArtinianRing.finite_of_finite_residueField (R ⧸ I)

private lemma compactSpace_of_finite_residueField : CompactSpace R := by
  letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  haveI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, completeSpace_iff_isComplete_univ.mp inferInstance⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU

  obtain ⟨I, hI_open, hI_sub⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU

  have : Finite (R ⧸ I) := finite_quotient_of_isOpen I hI_open
  obtain ⟨sec, hsec⟩ := (Ideal.Quotient.mk_surjective (I := I)).hasRightInverse
  refine ⟨Set.range sec, Set.finite_range sec, fun x _ ↦ ?_⟩

  refine Set.mem_iUnion₂.mpr ⟨sec (Ideal.Quotient.mk I x), ⟨_, rfl⟩, ?_⟩
  refine Set.mem_vadd_set.mpr ⟨x - sec (Ideal.Quotient.mk I x), hI_sub ?_, ?_⟩
  · show x - sec (Ideal.Quotient.mk I x) ∈ I
    rw [← Ideal.Quotient.eq]
    exact (hsec _).symm
  · show sec (Ideal.Quotient.mk I x) + (x - sec (Ideal.Quotient.mk I x)) = x
    abel

end IsProartinian

namespace Deformation.ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

instance instFiniteResidueField [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    Finite (ResidueField A) :=
  .of_surjective _ (IsResidueAlgebra.algebraMap_bijective 𝓞 A).surjective

instance instCompactSpace [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    CompactSpace A :=
  IsProartinian.compactSpace_of_finite_residueField

end Deformation.ProartinianCat


