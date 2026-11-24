-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:21.551663+00:00
-- url     : https://prove2.me/theorems/7d0ba62a-848c-4cce-a87e-dc0700347f36
-- title:
--   Kleiman St
-- statement:
--   Definitions and structural lemmas for Kleiman St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/KleimanSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
def NefOnV {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → V ≤ W →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ geoNum 1 W (fun _ => α)
def NefOnF {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (α : K → ℤ) : Prop :=
  ∀ W : Ideal (MRingOver F ι), IsProjVarF W 1 → V ≤ W → 0 ≤ I W 1 ![α]
def KleimanNefIntersectionNonneg : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι)) (n : ℕ)
    (a : Fin n → K → ℤ),
    IsMultiProjPrime V → charOf V ≠ 0 →
    ringKrullDim (MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ j, NefOnV V (a j)) → 0 ≤ geoNum n V a
def KleimanNefFStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) (a : Fin n → K → ℤ),
    IsFieldIntersection I → IsProjVarF V n → (∀ j, NefOnF I V (a j)) → 0 ≤ I V n a
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


