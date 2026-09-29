-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5c92f1ee-ebe5-5d4b-8514-9ede10a39d0e

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace"

namespace B2cSol

theorem eq_genericPoint_of_specializes_of_ne {X : Scheme.{u}} [IsIntegral X] {η x : X}
    (hηx : η ⤳ x) (hne : η ≠ x) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    η = genericPoint X := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hηU : η ∈ (U : Set X) := hηx.mem_open U.isOpen hxU

  let px := hU.primeIdealOf ⟨x, hxU⟩
  let pη := hU.primeIdealOf ⟨η, hηU⟩
  have hfx : hU.fromSpec px = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hfη : hU.fromSpec pη = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩

  have hsp : pη ⤳ px := by
    have key := (hU.fromSpec).isOpenEmbedding.isInducing.specializes_iff (x := pη) (y := px)
    rw [hfx, hfη] at key
    exact key.mp hηx
  have hle : pη.asIdeal ≤ px.asIdeal := (PrimeSpectrum.le_iff_specializes pη px).mpr hsp
  have hne' : pη ≠ px := by
    intro h; apply hne; rw [← hfx, ← hfη, h]
  have hlt : pη.asIdeal < px.asIdeal := lt_of_le_of_ne hle (fun h => hne' (PrimeSpectrum.ext h))

  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) px.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hhx : ringKrullDim (X.presheaf.stalk x) = px.asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height px.asIdeal (X.presheaf.stalk x)
  have hpx1 : px.asIdeal.height ≤ 1 := by
    have := hdim; rw [hhx] at this; exact_mod_cast this
  haveI : px.asIdeal.FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (lt_of_le_of_lt hpx1 (by simp)))
  have hpη : pη.asIdeal.height < 1 := lt_of_lt_of_le (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt) hpx1
  have hpη0 : pη.asIdeal.height = 0 := ENat.lt_one_iff_eq_zero.mp hpη
  have hmin : pη.asIdeal ∈ minimalPrimes Γ(X, U) := Ideal.height_eq_zero_iff.mp hpη0
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hmin
  have hpηbot : pη = ⊥ := PrimeSpectrum.ext hmin

  rw [← hfη, hpηbot, ← genericPoint_eq_bot_of_affine]
  exact genericPoint_eq_of_isOpenImmersion hU.fromSpec

end B2cSol

open B2cSol in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) (x : X)
    (hx : x ∈ (Scheme.Modules.zeroSchemeIdeal s).support) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    Maximal (fun C' : Set X => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal s).support) (closure {x}) := by
  set D := (Scheme.Modules.zeroSchemeIdeal s).support with hD
  have hξ : genericPoint X ∉ D := hD ▸ hM.genericPoint_notMem_support_zeroSchemeIdeal_monoidalV2 s hs
  refine ⟨⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.2 hx) D.isClosed⟩, ?_⟩
  intro C hC hxC

  have hη := hC.1.isGenericPoint_genericPoint_closure
  set η := hC.1.genericPoint with hηdef
  have hCD : closure C ⊆ (D : Set X) := closure_minimal hC.2 D.isClosed
  have hηD : η ∈ (D : Set X) := hCD hη.mem
  have hxC' : x ∈ closure C := subset_closure (hxC (subset_closure (Set.mem_singleton x)))
  have hηx : η ⤳ x := hη.specializes hxC'

  have hηeq : η = x := by
    by_contra hne
    have := eq_genericPoint_of_specializes_of_ne hηx hne hdim
    exact hξ (this ▸ hηD)

  intro c hc
  have : c ∈ closure C := subset_closure hc
  rw [← hη.def, hηeq] at this
  exact this

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_maximal_isIrreducible_closure_singleton_of_mem_support_of_ringKrullDim_le_one (solution)
