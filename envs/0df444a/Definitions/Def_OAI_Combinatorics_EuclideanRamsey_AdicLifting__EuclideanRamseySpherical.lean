-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:02:57.530107+00:00
-- url     : https://prove2.me/theorems/48fb83e7-b35e-48d2-962c-0b3f9d211d94
-- title:
--   Rational extension of lattice homomorphisms
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $R$ be a commutative $\mathbb Q$-algebra and $f:\mathbb Z^k\to R$ an additive homomorphism. Its rational extension is the $\mathbb Q$-linear map
--   $$
--   \hat f:\mathbb Q^k\to R,\qquad\hat f(v)=\sum_{j=1}^kv_j\,f(e_j),
--   $$
--   where $e_1,\dots,e_k$ are the standard basis vectors. The module records that $\hat f(e_j)=f(e_j)$, so $\hat f$ extends $f$ from the lattice to the rational vector space it spans.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical

namespace OAI

universe uRing uGroup uSemigroup uModule uModuleTarget uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct
namespace EuclideanRamsey

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
open Finset

end NilpotentLog

section LogCharacter
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
  {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)

variable {G : Type uGroup} [AddCommGroup G] (χ : Multiplicative G →* R)
  (hχ : ∀ γ : G, χ (Multiplicative.ofAdd γ) - 1 ∈ I)

end LogCharacter

section LatticeLog
variable {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]

def rationalExtension (f : (Fin k → ℤ) →+ R) : (Fin k → ℚ) →ₗ[ℚ] R where
  toFun v := ∑ j, v j • f (Pi.single j 1)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [mul_smul, Finset.smul_sum]

end LatticeLog

section AdicLifting
variable {R : Type uRing} {M : Type uModule} {N : Type uModuleTarget} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R N]

end AdicLifting

section IntersectionLifting
variable {R : Type uRing} [CommRing R] [IsNoetherianRing R]
  {ι : Type uIndex} [Fintype ι] (I : Ideal R) (J : ι → Ideal R)

end IntersectionLifting

section Construction
variable {k : ℕ}

@[simp] lemma rationalExtension_single {R : Type uRing} [CommRing R] [Algebra ℚ R]
    (f : Lattice k →+ R) (a : Fin k) :
    rationalExtension f (Pi.single a 1) = f (Pi.single a 1) := by
  classical
  simp [rationalExtension, Pi.single_apply]

end Construction

end EuclideanRamsey

end

end OAI


