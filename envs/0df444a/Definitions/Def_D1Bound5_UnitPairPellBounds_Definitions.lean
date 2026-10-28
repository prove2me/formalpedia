-- Prove2me | Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions
-- name    : D1Bound5_UnitPairPellBounds_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:30:53.912964+00:00
-- url     : https://prove2.me/theorems/c505e379-1d3d-47fd-a4f5-8244730eac34
-- title:
--   Unit Pair Pell Bounds
-- statement:
--   Definitions for unit pair pell bounds in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/UnitPairPellBounds.lean, lines 7-17, SHA-256 fd49ea4fdd430107d4e1829868b8b6395961a3e5bc7f50289f46971ac867b203. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions

section
namespace D1Bound5

theorem UnitPairPellDescription.map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℤ) (w z : R) (h : UnitPairPellDescription d w z) :
    UnitPairPellDescription d (f w) (f z) := by
  rcases h with h | h
  · left
    obtain ⟨u,v,hv,hPell,hplus | hminus⟩ := h
    · exact ⟨u,v,hv,hPell,Or.inl (by rw [hplus,map_intCast])⟩
    · exact ⟨u,v,hv,hPell,Or.inr (by rw [hminus,map_neg,map_intCast])⟩
  · right
    obtain ⟨u,v,hv,hPell,hz⟩ := h
    exact ⟨u,v,hv,hPell,by rw [hz,map_mul,map_intCast]⟩









open scoped NumberField
open Module



end D1Bound5
end


