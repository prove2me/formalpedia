-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:41.779588+00:00
-- url     : https://prove2.me/theorems/95f5dac3-c9a2-40ef-a75d-45891c5919d3
-- title:
--   Is Vertical Div Of Is Vertical Divisor
-- statement:
--   Definitions and structural lemmas for Is Vertical Div Of Is Vertical Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
section Points
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
def coords (pt : MRingOver R ι →ₐ[R] Ω) : (Σ k, ι k) → Ω := fun p => pt (X p)
end Points
section Lines
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
end Lines
section Flags
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
def scaleBasis (u : Module.Basis (Fin N) Ω E) {ω : Fin N → Ω} (hω : ∀ l, ω l ≠ 0) :
    Module.Basis (Fin N) Ω E :=
  u.unitsSMul fun l => Units.mk0 (ω l) (hω l)
end Flags
section Twisted
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
end Twisted
section Generic
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
end Generic
section Degrees
variable {K : Type*} [Fintype K]
end Degrees
section Triangular
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
end Triangular
section MultiHomog
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
end MultiHomog
section FlagPairs
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
end FlagPairs
section Numbers
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end Numbers
section Divisors
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Divisors
section Monomials
def listMono {σ : Type*} [DecidableEq σ] (l : List σ) : σ →₀ ℕ :=
  Multiset.toFinsupp (l : Multiset σ)
end Monomials
section Koszul
variable {N : ℕ}
def koszulTerm (ls : List (Fin N)) (k : ℕ) : MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  ((ls.take k).map fun l => X (Sum.inr l)).prod * ((ls.drop (k + 1)).map fun l => X (Sum.inl l)).prod
def koszulExp (G : MvPolynomial (Fin N) ℤ) (i : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  ∑ μ ∈ G.support, C (G.coeff μ) *
    ∑ k : Fin (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).length,
      if (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ).get k = i then koszulTerm (IndefiniteRowSideFullHecke.NumbersDVR.monoList μ) k else 0
end Koszul
section PairNumbers
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}
def koszulList (m m' : Fin N → K → ℤ) (ls : List (Fin N)) (k : ℕ) : List (K → ℤ) :=
  (ls.take k).map m' ++ (ls.drop (k + 1)).map m
end PairNumbers
section Vertical
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Vertical
section ProjBundle
variable {Ω : Type*} [Field Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N : ℕ}
def lineMap (t : Fin N → Φ) : MvPolynomial (Fin N) Ω →+* Polynomial Φ :=
  eval₂Hom (Polynomial.C.comp (algebraMap Ω Φ)) fun l => Polynomial.C (t l) * Polynomial.X
variable {K : Type*}
def genericLineMap (t : Fin N → Φ) : MvPolynomial (K ⊕ Fin N) Ω →+* MvPolynomial (Option K) Φ :=
  eval₂Hom ((C : Φ →+* MvPolynomial (Option K) Φ).comp (algebraMap Ω Φ))
    (Sum.elim (fun k => X (some k)) fun l => C (t l) * X none)
variable [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {M : ℕ}
def bundleToExt (ι : K → Type) (M : ℕ) :
    (Σ o, NumbersDVR.bundleIdx ι M o) → Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι (Fin M) o
  | ⟨none, l⟩ => ⟨none, l⟩
  | ⟨some k, i⟩ => ⟨some k, i⟩
def extToBundle (ι : K → Type) (M : ℕ) :
    (Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι (Fin M) o) → Σ o, NumbersDVR.bundleIdx ι M o
  | ⟨none, l⟩ => ⟨none, l⟩
  | ⟨some k, i⟩ => ⟨some k, i⟩
variable {F : Type*} [Field F] [Algebra F Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
end ProjBundle
end FlagTypings
end GroundTheory.Heights₂.Heights


