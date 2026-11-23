-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:23.530802+00:00
-- url     : https://prove2.me/theorems/38efa7f5-99d4-466a-87a3-66f17618d4e0
-- title:
--   Mul Vec Injective Of Ker
-- statement:
--   Definitions and structural lemmas for Mul Vec Injective Of Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
namespace GramDeterminantPositive
open Matrix
open scoped ComplexOrder
section Mat
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
end Mat
section NF
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def cmat (A : HLat K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) : Matrix A.ι (Fin m) ℂ :=
  Matrix.of fun k i => φ (A.b.repr (f i) k)
def hmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) : Matrix A.ι A.ι ℂ :=
  Matrix.of fun k l => φ (h (A.b k) (A.b l))
def rho (φ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (φ.comp (starRingEnd K))
def gmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    Matrix (Fin m) (Fin m) ℂ :=
  (cmat A φ f)ᴴ * hmat A h φ * cmat A φ f
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
section Hyp
variable (hC1 : ∀ i j, IsCM (h (A.b i) (A.b j)))
  (hC3 : ∀ (v : InfinitePlace K) i j,
    Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j)))
include hC3
end Hyp
def piv (v : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (v.embedding.comp (starRingEnd K))
end NF
end GramDeterminantPositive
open NumberField Formalism.BasicNotions PI.Dv GramDeterminantPositive Matrix
end PI.DvRows


