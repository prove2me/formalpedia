-- Prove2me | Definitions.Def_Deformations_MvPowerSeriesObj
-- name    : Deformations_MvPowerSeriesObj
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/e451a818-1160-5c71-aa4f-279ebe03d01d
-- title:
--   Power series rings as objects of the pro-Artinian category
-- statement:
--   This module places multivariate formal power series rings in the category $\mathcal{C}_{\mathcal O}$ of local pro-Artinian $\mathcal O$-algebras. Two preliminary lemmas concern a commutative topological local ring $R$ that is pro-Artinian (linearly topologised by ideals, $T_0$, complete, and with $R/I$ Artinian for every open ideal $I$): every $x$ in the maximal ideal of $R$ is topologically nilpotent, because each open ideal contains a power of the maximal ideal; and, for a finite index type $\sigma$, a family $x : \sigma \to R$ with all $x_j$ in the maximal ideal satisfies Mathlib's `MvPowerSeries.HasEval`, so power series may be evaluated at it (the cofiniteness condition being vacuous for finite $\sigma$).
--
--   For a commutative ring $\mathcal O$ and an index type $\sigma$, $\mathrm{MvPowerSeries}\,\sigma\,\mathcal O$ carries the product topology over that of $\mathcal O$; it is compact when $\mathcal O$ is. When $\mathcal O$ is local, each variable $X_j$ lies in the maximal ideal (its constant coefficient vanishes), the structure map $\mathcal O \to \mathcal O[\![\sigma]\!]$ is a local homomorphism, and the residue field is reached from $\mathcal O$, since a power series is a unit modulo the maximal ideal precisely according to its constant term; if moreover $\mathcal O$ is Noetherian with the adic topology and compact, the power series ring is pro-Artinian, all open quotients being finite. Combining these gives `IsLocalProartinianAlgebra 𝓞 (MvPowerSeries σ 𝓞)`.
--
--   Finally, for $\mathcal O$ local Noetherian with finite residue field and complete for the $\mathfrak m$-adic topology, `mvPowerSeriesObj 𝓞 n` is the object of `ProartinianCat 𝓞` with carrier $\mathcal O[\![X_1,\dots,X_n]\!]$ ($n$ variables indexed by `Fin n`), and `mvPowerSeriesObjX j` denotes its $j$-th variable, shown to lie in the maximal ideal.
--
--   **Relation to Mathlib.** `MvPowerSeries`, its product (`WithPiTopology`) topology and the evaluation condition `MvPowerSeries.HasEval` are Mathlib's; the predicates [`IsProartinian`](../def/Deformations_IsProartinian.html#L185), [`IsResidueAlgebra`](../def/Deformations_IsResidueAlgebra.html#L15), `IsLocalProartinianAlgebra` and the category `ProartinianCat` are the project's own.
--
--   **Where it is used.** The objects $\mathcal O[\![X_1,\dots,X_n]\!]$ are the free objects of the deformation category $\mathcal{C}_{\mathcal O}$: every object with finite-dimensional tangent space is a quotient of one of them, and power series rings in this form are the source of the presentations of deformation rings and of the power series ring over which the Taylor–Wiles patching argument is run.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (portions (≈8%): `FLT/Deformations/Categories.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_MvPowerSeriesObj.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace Deformation

open CategoryTheory IsLocalRing MvPowerSeries

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

section Nilpotence

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLocalRing R] [IsProartinian R]

lemma isTopologicallyNilpotent_of_mem_maximalIdeal {x : R} (hx : x ∈ maximalIdeal R) :
    IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent,
    (IsLinearTopology.hasBasis_open_ideal (R := R)).tendsto_right_iff]
  intro I hI
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN (Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n))

lemma hasEval_of_forall_mem_maximalIdeal {σ : Type*} [Finite σ] {x : σ → R}
    (hx : ∀ j, x j ∈ maximalIdeal R) : MvPowerSeries.HasEval x where
  hpow j := isTopologicallyNilpotent_of_mem_maximalIdeal (hx j)
  tendsto_zero := by
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

end Nilpotence

section Object

open MvPowerSeries.WithPiTopology

variable (𝓞 : Type u) [CommRing 𝓞] (σ : Type)

omit [CommRing 𝓞] in

lemma compactSpace_mvPowerSeries [TopologicalSpace 𝓞] [CompactSpace 𝓞] :
    CompactSpace (MvPowerSeries σ 𝓞) :=
  inferInstanceAs (CompactSpace ((σ →₀ ℕ) → 𝓞))

lemma X_mem_maximalIdeal [IsLocalRing 𝓞] (j : σ) :
    MvPowerSeries.X j ∈ maximalIdeal (MvPowerSeries σ 𝓞) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact fun h => h.ne_zero rfl

lemma isProartinian_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [TopologicalSpace 𝓞]
    [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsProartinian (MvPowerSeries σ 𝓞) := by
  haveI : CompactSpace (MvPowerSeries σ 𝓞) := compactSpace_mvPowerSeries 𝓞 σ
  exact
    { isArtinianRing_quotient := fun I hI => by
        have : Finite (MvPowerSeries σ 𝓞 ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
        exact isArtinian_of_finite }

lemma isLocalHom_algebraMap_mvPowerSeries [IsLocalRing 𝓞] :
    IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) := by
  constructor
  intro a ha
  rw [← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C] at ha
  exact ha

lemma isResidueAlgebra_mvPowerSeries [IsLocalRing 𝓞] :
    IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  constructor
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  show residue _ _ = residue _ _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp [← MvPowerSeries.c_eq_algebraMap]

lemma isLocalProartinianAlgebra_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsLocalProartinianAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  haveI : IsProartinian (MvPowerSeries σ 𝓞) := isProartinian_mvPowerSeries 𝓞 σ
  haveI : IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) :=
    isLocalHom_algebraMap_mvPowerSeries 𝓞 σ
  haveI : IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := isResidueAlgebra_mvPowerSeries 𝓞 σ
  exact ⟨⟩

end Object

section Category

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
variable [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]

noncomputable def mvPowerSeriesObj (n : ℕ) : ProartinianCat 𝓞 where
  carrier := MvPowerSeries (Fin n) 𝓞
  topologicalSpace :=
    letI := (maximalIdeal 𝓞).adicTopology
    WithPiTopology.instTopologicalSpace 𝓞
  isLocalProartinianAlgebra :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : IsAdicTopology 𝓞 := ⟨rfl⟩
    letI : CompactSpace 𝓞 := compactSpace_of_finite_residueField
    isLocalProartinianAlgebra_mvPowerSeries 𝓞 (Fin n)

variable {𝓞}

noncomputable def mvPowerSeriesObjX {n : ℕ} (j : Fin n) : (mvPowerSeriesObj 𝓞 n).carrier :=
  MvPowerSeries.X j

lemma mvPowerSeriesObjX_mem_maximalIdeal {n : ℕ} (j : Fin n) :
    mvPowerSeriesObjX (𝓞 := 𝓞) j ∈ maximalIdeal (mvPowerSeriesObj 𝓞 n).carrier :=
  X_mem_maximalIdeal 𝓞 (Fin n) j

end Category

end ProartinianCat

end Deformation


