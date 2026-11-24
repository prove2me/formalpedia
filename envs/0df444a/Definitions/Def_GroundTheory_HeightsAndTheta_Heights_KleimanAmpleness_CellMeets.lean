-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CellMeets
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CellMeets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:47.117855+00:00
-- url     : https://prove2.me/theorems/cdb66e02-d457-4278-8f3c-3c6435c36c68
-- title:
--   Cell Meets
-- statement:
--   Definitions and structural lemmas for Cell Meets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CellMeets.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]
def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0
open Classical in

def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥
variable [LinearOrder K] [∀ k, LinearOrder (ι k)]
open Classical in

def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0
def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1
def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)
def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)
abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


