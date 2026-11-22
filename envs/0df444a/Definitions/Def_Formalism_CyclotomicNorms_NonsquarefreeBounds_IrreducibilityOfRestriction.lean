-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:31:22.243077+00:00
-- url     : https://prove2.me/theorems/9f9a1945-6c42-48b4-b331-135c90ba1db5
-- title:
--   Irreducibility Of Restriction
-- statement:
--   Definitions and structural lemmas for Irreducibility Of Restriction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
section PrimeTo
variable {M : Type*} [Monoid M]
end PrimeTo
section Frob
variable {g : ℕ} [hg : Fact g.Prime]
end Frob
section Roots
variable {g : ℕ} [hg : Fact g.Prime]
structure GoodPoly (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  coeff0 : f.coeff 0 ≠ 0
  sqf : Squarefree f
variable {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}
end Roots
section Cycle
variable {g : ℕ} [hg : Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}
end Cycle
section Orbits
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
def cyc (i : α) : Finset α := Finset.univ.filter (fun j => σ.SameCycle i j)
def blocks : Finset (Finset K) := Finset.univ.image (fun i => (cyc σ i).image L)
variable {σ L}
end Orbits
section Lin
variable {K : Type*} [Field K] {N : ℕ}
def repGL : GL (Fin N) K →* Module.End K (Fin N → K) :=
  (MonoidHomClass.toMonoidHom (Matrix.toLinAlgEquiv' :
    Matrix (Fin N) (Fin N) K ≃ₐ[K] Module.End K (Fin N → K))).comp (Units.coeHom _)
def glEquiv (A : GL (Fin N) K) : (Fin N → K) ≃ₗ[K] (Fin N → K) :=
  LinearEquiv.ofLinearMap (repGL A) (repGL A⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])
end Lin
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder


