-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:31.576844+00:00
-- url     : https://prove2.me/theorems/21a75455-59f1-4880-a7ce-2c49e7f129c8
-- title:
--   PUnit Basis
-- statement:
--   Definitions and structural lemmas for PUnit Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
structure PLat (c : K →+* K) (h : V → V → K) (O : Subring K) (L : AddSubgroup V) (p : ℕ) : Prop where
  herm : Herm4 c h
  prime : p.Prime
  cO : ∀ t ∈ O, c t ∈ O
  smul : ∀ o ∈ O, ∀ x ∈ L, o • x ∈ L
  int : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O
  unim : ∀ x, (∀ y ∈ L, h x y ∈ O) → x ∈ L
  full : ∀ x : V, ∃ n : ℕ, 0 < n ∧ (n : K) • x ∈ L
  nat : ∀ x ∈ L, ∃ n : ℕ, h x x = (n : K)
  crit : ∃ ω ∈ O, ∀ t ∈ O, (∃ k : ℤ, t + c t = (p : K) * k) → (∃ k : ℤ, ω * t + c (ω * t) = (p : K) * k) →
    ∃ t' ∈ O, t = (p : K) * t'
def Good (h : V → V → K) (L : AddSubgroup V) (p : ℕ) {ι : Type} (v : ι → V) (n : ι → ℕ) : Prop :=
  (∀ i, v i ∈ L) ∧ (∀ i, h (v i) (v i) = (n i : K)) ∧ (∀ i, ¬ p ∣ n i) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
section Desc
variable (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ} (G : Good h L p v n)
  (hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k)
include P G hdiv
end Desc
namespace Test
end Test
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
end


