-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:04.052863+00:00
-- url     : https://prove2.me/theorems/44cb3dc0-a249-52ad-a0ef-8b323e86e9b6
-- title:
--   An Hol Fam Of Hol To
-- statement:
--   Definitions and structural lemmas for An Hol Fam Of Hol To, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
section Lin
variable {g g' : ℕ}
def anLin (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) : MvPolynomial (Fin 1 × Fin g') ℂ :=
  ∑ k : Fin g', MvPolynomial.C (A (Pi.single k 1) p.2) * MvPolynomial.X ((0 : Fin 1), k)
theorem anLin_mem (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) : anLin A p ∈ orig ℂ (Fin 1 × Fin g') :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (X_mem_orig _)
end Lin
variable {Y : Scheme.{0}}
section Two
variable {g : ℕ}
abbrev anKap : Fin 2 × Fin g ≃ Fin (2 * g) := finProdFinEquiv
def anPr (i : Fin 2) : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * g) => ℂ) (anKap (i, j))
abbrev anSum : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ) := anPr 0 + anPr 1
def anRen (m : ℕ) : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m :=
  jetMap (fun p => MvPolynomial.X (anKap.symm p.2)) fun _ => X_mem_orig _
end Two
section Law
variable {X : Scheme.{0}} {G : Over X} [MonObj G] {g : ℕ}
def anJX (u : Sp ℂ ⟶ X) (ex : (Fin g → ℂ) → (Over.mk u ⟶ G)) (hol : IsHolFam fun z => (ex z).left) (m : ℕ) :
    overAt u (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt (fun z => (ex z).left) hol m)
    (jetPt_over (fun z => (ex z).left) hol G.hom u (fun z => Over.w (ex z)) m)
end Law
end ReciprocityTheory.ChartRestriction.G.PullbackSections


