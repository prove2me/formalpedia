-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- name    : ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:51.982002+00:00
-- url     : https://prove2.me/theorems/6cd5108f-d369-4fc0-9cbe-e1a166065dbe
-- title:
--   Det Poly Mul Cayley Omega Pow
-- statement:
--   Definitions and structural lemmas for Det Poly Mul Cayley Omega Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
namespace ReciprocityTheory.PGsh
section General
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
end General
variable {n : ℕ}
section ChainRule
variable {R : Type*} [CommRing R]
def linSub (g : Matrix (Fin n) (Fin n) R) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R :=
  aeval fun p => ∑ k, C (g p.1 k) * X (k, p.2)
def dOp {m : ℕ} (r c : Fin m → Fin n) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  (List.ofFn fun t => ((pderiv (r t, c t) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod
end ChainRule
section Integer
def onePt : Fin n × Fin n → ℤ := fun v => (1 : Matrix (Fin n) (Fin n) ℤ) v.1 v.2
def funMat (ρ : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if a = ρ b then 1 else 0
def yP (σ τ : Fin n → Fin n) (S : Finset (Fin n)) : MvPolynomial (Fin n × Fin n) ℤ :=
  ∏ b, if b ∈ S then (if τ b = σ b then 1 else 0) else X (τ b, b)
def fibOp (σ : Fin n → Fin n) {s : ℕ} (φ : Fin n → Fin s) (k : Fin s) :
    Module.End ℤ (MvPolynomial (Fin n × Fin n) ℤ) :=
  (List.ofFn fun j => if φ j = k then ((pderiv (σ j, j) : Derivation ℤ _ _) :
    MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ) else 1).prod
end Integer
section Map
variable {R : Type*} [CommRing R]
end Map
end ReciprocityTheory.PGsh


