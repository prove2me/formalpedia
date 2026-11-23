-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:02.296626+00:00
-- url     : https://prove2.me/theorems/34dcc141-8467-447d-80ff-13880bcd6ab0
-- title:
--   Pre Mem Irreducible Components
-- statement:
--   Definitions and structural lemmas for Pre Mem Irreducible Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
section Top
variable {α : Type*} [TopologicalSpace α]
def compsH (T : Set α) : Set (Set α) :=
  {C | Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C}
end Top
section Alg
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}
def parPrime (f : Fin n → A) (i : Fin n) : Ideal A :=
  (Ideal.span {algebraMap A S (f i)}).comap (algebraMap A S)
end Alg
noncomputable section
section Pts
variable {W : Scheme.{0}} {U : W.Opens}
theorem fromSpec_mem (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) : hU.fromSpec P ∈ U := by
  have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
  rwa [hU.range_fromSpec] at this
end Pts
end
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages


