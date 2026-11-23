-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
-- name    : ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:56.84372+00:00
-- url     : https://prove2.me/theorems/7b7437ee-7257-4d92-b71e-a1d7c70a61a4
-- title:
--   Restricted Hopf Order Approximation Statement
-- statement:
--   Definitions and structural lemmas for Restricted Hopf Order Approximation Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RestrictedHopfOrderApproximationStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
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
def psiW {p : ℕ} [Fact p.Prime] {g r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) :
    (Fin r → ZMod p) →+ Nb p g :=
  (Matrix.mulVecLin (Bw.map PadicInt.toZMod)).toAddMonoidHom
def RestrictedHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (a : O), a * a = a →
    ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ a)) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL a)) ≃ₗ[R] (Fin d → R)) →
    ∃ AW : HopfOrder (C := C) R (Fin r → ZMod p),
      AW.carrier = H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)) ∧
      HasLen v R (OmAA AW.carrier) (v (algebraMap R C (p : R)) ^ d)
def RestrictedHopfOrderApproximationStatement : Prop :=
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
    ∀ (lam : Fin r → R) (dj : R),
      dj • lam ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i) →
      v (algebraMap R C cp) ≤ v (algebraMap R C dj) →
      ∃ f ∈ H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)), ∀ x : Fin r → ℤ_[p],
        v (f (fun i => PadicInt.toZMod (x i)) -
          algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i))) < v (algebraMap R C dj)
end ReciprocityTheory.PGsh.Up


