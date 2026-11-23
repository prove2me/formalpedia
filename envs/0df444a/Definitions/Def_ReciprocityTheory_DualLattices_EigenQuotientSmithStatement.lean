-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EigenQuotientSmithStatement
-- name    : ReciprocityTheory_DualLattices_EigenQuotientSmithStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:41.113883+00:00
-- url     : https://prove2.me/theorems/a1885145-99a9-43e9-8b1f-c5b1256c44be
-- title:
--   Eigen Quotient Smith Statement
-- statement:
--   Definitions and structural lemmas for Eigen Quotient Smith Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenQuotientSmithStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
def EigenQuotientSmithStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ X : NNReal, HasLen v R (xMod H e π w) X →
    ∃ (Λ : Matrix (Fin r) (Fin r) R) (dj : Fin r → R), IsUnit Λ.det ∧
      (∀ j, dj j • Λ j ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i)) ∧
      (∀ j, v (algebraMap R C cp) ≤ v (algebraMap R C (dj j))) ∧
      X = ∏ j, v (algebraMap R C (dj j))
end ReciprocityTheory.PGsh.Up


