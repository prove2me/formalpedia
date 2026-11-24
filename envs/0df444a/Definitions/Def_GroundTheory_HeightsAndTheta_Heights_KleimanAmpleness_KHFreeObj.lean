-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeObj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:09.602216+00:00
-- url     : https://prove2.me/theorems/9b007490-fe47-40f0-951b-6459d81697e3
-- title:
--   KHFree Obj
-- statement:
--   Definitions and structural lemmas for KHFree Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/KHFreeObj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgSFreeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace KHFree
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def negSet (a : (Σ k, ι k) → ℤ) : ∀ k, Finset (ι k) :=
  fun k => Finset.univ.filter fun i => a ⟨k, i⟩ < 0
def blockSum (a : (Σ k, ι k) → ℤ) : K → ℤ :=
  fun k => ∑ i, a ⟨k, i⟩
def posExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (a p).toNat
def negExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (-a p).toNat
theorem monomial_negExp_mem (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ)
    (h : ∀ k, negSet a k ⊆ I k) : (monomial (negExp a) (1 : S) : MRingOver S ι) ∈ KH.cellMon S I := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod]
  refine Submonoid.prod_mem _ fun p hp => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  refine ⟨p.1, p.2, h p.1 ?_, rfl⟩
  have hp' : (negExp a) p ≠ 0 := Finsupp.mem_support_iff.mp hp
  simp only [negExp, Finsupp.coe_equivFunOnFinite_symm] at hp'
  simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and]
  show a p < 0
  omega
open Classical in

def monoFrac (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ) :
    LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  if h : ∀ k, negSet a k ⊆ I k then
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (monomial (posExp a) 1))
      ⟨monomial (negExp a) 1, monomial_negExp_mem S I a h⟩
  else 0
def CombCell (ι : K → Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  {I : KH.Cell K ι n // ∀ k, J k ⊆ I.1 k}
abbrev CombC (S : Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  CombCell ι J n → S
variable [LinearOrder K] [∀ k, LinearOrder (ι k)]
open Classical in

def combD (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) :
    CombC S J n →ₗ[S] CombC S J (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1.1 k,
    if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
        ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
      KH.faceSign I.1.1 k i • LinearMap.proj (R := S) (φ := fun _ : CombCell ι J n => S)
        ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
    else 0
def combB (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) : (n : ℕ) → Submodule S (CombC S J n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (combD S J n)
end KHFree
namespace KHFree
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def singOne (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) : CombC S J n :=
  fun I => if ∀ k, J k = ∅ → (I.1.1 k).card = 1 then 1 else 0
open Classical in

def embed (S : Type) [CommRing S] (a : (Σ k, ι k) → ℤ) (n : ℕ) :
    CombC S (negSet a) n →ₗ[S] KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
  LinearMap.pi fun I => if h : ∀ k, negSet a k ⊆ I.1 k then
    (LinearMap.toSpanSingleton S _ (monoFrac S I.1 a)).comp
      (LinearMap.proj (R := S) (φ := fun _ : CombCell ι (negSet a) n => S) ⟨I, h⟩)
  else 0
end KHFree
end
end GroundTheory.Heights₂.Heights.Kleiman


