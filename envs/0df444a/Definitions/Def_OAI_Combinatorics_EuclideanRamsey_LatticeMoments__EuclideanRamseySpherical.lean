-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:00:30.93513+00:00
-- url     : https://prove2.me/theorems/950cdcdf-da1e-4a1a-98f7-7cbcf9ce6984
-- title:
--   Mass and moments of rational signed measures on $\mathbb Z^k$
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $\mathbb Q[\mathbb Z^k]$ be the group algebra of the lattice $\mathbb Z^k$ over $\mathbb Q$, the ring of rational Laurent polynomials in $k$ variables. An element $\nu=\sum_\gamma\nu_\gamma[\gamma]$ is a finitely supported rational signed measure on $\mathbb Z^k$, and multiplication is convolution.
--
--   1. **Moments.** The mass $\sum_\gamma\nu_\gamma$, the first moments $\sum_\gamma\nu_\gamma\gamma_a$, and the second moments $\sum_\gamma\nu_\gamma\gamma_a\gamma_b$.
--   2. **Coefficient functionals.** For $g:\mathbb Z^k\to\mathbb Q$, the linear functional $\nu\mapsto\sum_\gamma\nu_\gamma g(\gamma)$. Mass and moments are of this form, so they are $\mathbb Q$-linear and commute with finite sums.
--   3. **Augmentation.** The algebra homomorphism $\mathbb Q[\mathbb Z^k]\to\mathbb Q$ sending every $[\gamma]$ to $1$, which equals the mass. Hence the mass is multiplicative. The unit $[0]$ has mass $1$ and vanishing first and second moments.
--
--   The group algebra is Noetherian, since it is a finitely generated $\mathbb Q$-algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical

namespace OAI

universe uIndex

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
namespace EuclideanRamsey

abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)

def mass {k : ℕ} (ν : LatticeRing k) : ℚ := ν.coeff.sum fun _ q => q

def firstMoment {k : ℕ} (ν : LatticeRing k) (a : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a

def secondMoment {k : ℕ} (ν : LatticeRing k) (a b : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a * γ b

section Algebra
variable {k : ℕ}

instance latticeNoetherian : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)

def augmentation : LatticeRing k →ₐ[ℚ] ℚ :=
  AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

lemma augmentation_eq_mass (x : LatticeRing k) : augmentation x = mass x := by
  simp only [augmentation, AddMonoidAlgebra.lift_apply, MonoidHom.one_apply, smul_eq_mul, mul_one, mass]

@[simp] lemma augmentation_monomial (γ : Lattice k) :
    augmentation (AddMonoidAlgebra.single γ 1) = 1 := by
  simp [augmentation]

def coefficientFunctional (g : Lattice k → ℚ) : LatticeRing k →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

lemma coefficientFunctional_apply (g : Lattice k → ℚ) (x : LatticeRing k) :
    coefficientFunctional g x = x.coeff.sum (fun γ q => q * g γ) := rfl

@[simp] lemma coefficientFunctional_single (g : Lattice k → ℚ) (γ : Lattice k) (q : ℚ) :
    coefficientFunctional g (AddMonoidAlgebra.single γ q) = q * g γ := by
  simp [coefficientFunctional, Finsupp.linearCombination_apply]

lemma mass_linear : (mass : LatticeRing k → ℚ) = coefficientFunctional (fun _ => 1) := by
  funext x
  simp [coefficientFunctional_apply, mass]

lemma secondMoment_linear (a b : Fin k) :
    (fun x : LatticeRing k => secondMoment x a b) =
      coefficientFunctional (fun γ => (γ a : ℚ) * γ b) := by
  funext x
  simp only [secondMoment, coefficientFunctional_apply, mul_assoc]

@[simp] lemma mass_add (x y : LatticeRing k) : mass (x+y) = mass x + mass y := by
  simp only [mass_linear, map_add]
@[simp] lemma mass_smul (r : ℚ) (x : LatticeRing k) : mass (r • x) = r * mass x := by
  simp only [mass_linear, map_smul, smul_eq_mul]
@[simp] lemma mass_zero : mass (0 : LatticeRing k) = 0 := by simp only [mass_linear, map_zero]
@[simp] lemma mass_single (γ : Lattice k) (q : ℚ) : mass (AddMonoidAlgebra.single γ q) = q := by
  simp [mass_linear]
@[simp] lemma mass_mul (x y : LatticeRing k) : mass (x*y) = mass x * mass y := by
  simp only [← augmentation_eq_mass, map_mul]
@[simp] lemma firstMoment_add (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x+y) a = firstMoment x a + firstMoment y a := by
  change coefficientFunctional _ (x+y) = _ + _
  exact map_add _ _ _
@[simp] lemma firstMoment_smul (r : ℚ) (x : LatticeRing k) (a : Fin k) :
    firstMoment (r • x) a = r * firstMoment x a := by
  change coefficientFunctional _ (r • x) = _ * _
  exact map_smul _ _ _
@[simp] lemma firstMoment_zero (a : Fin k) : firstMoment (0 : LatticeRing k) a = 0 := by
  exact map_zero (coefficientFunctional (k := k) (fun γ => γ a))
@[simp] lemma firstMoment_single (γ : Lattice k) (q : ℚ) (a : Fin k) :
    firstMoment (AddMonoidAlgebra.single γ q) a = q * γ a := coefficientFunctional_single _ _ _
@[simp] lemma secondMoment_add (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x+y) a b = secondMoment x a b + secondMoment y a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_add]
@[simp] lemma secondMoment_smul (r : ℚ) (x : LatticeRing k) (a b : Fin k) :
    secondMoment (r • x) a b = r * secondMoment x a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_smul, smul_eq_mul]
@[simp] lemma secondMoment_zero (a b : Fin k) : secondMoment (0 : LatticeRing k) a b = 0 := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_zero]
@[simp] lemma secondMoment_single (γ : Lattice k) (q : ℚ) (a b : Fin k) :
    secondMoment (AddMonoidAlgebra.single γ q) a b = q * γ a * γ b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, coefficientFunctional_single, mul_assoc]

@[simp] lemma mass_sub (x y : LatticeRing k) : mass (x-y) = mass x - mass y := by
  simp only [mass_linear, map_sub]
@[simp] lemma firstMoment_sub (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x-y) a = firstMoment x a - firstMoment y a := by
  exact map_sub (coefficientFunctional (k := k) (fun γ => γ a)) x y
@[simp] lemma secondMoment_sub (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x-y) a b = secondMoment x a b - secondMoment y a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_sub]
@[simp] lemma mass_one : mass (1 : LatticeRing k) = 1 := by
  change mass (AddMonoidAlgebra.single 0 1) = 1
  simp
@[simp] lemma firstMoment_one (a : Fin k) : firstMoment (1 : LatticeRing k) a = 0 := by
  change firstMoment (AddMonoidAlgebra.single 0 1) a = 0
  simp
@[simp] lemma secondMoment_one (a b : Fin k) : secondMoment (1 : LatticeRing k) a b = 0 := by
  change secondMoment (AddMonoidAlgebra.single 0 1) a b = 0
  simp

@[simp] lemma mass_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) :
    mass (∑ i ∈ t, x i) = ∑ i ∈ t, mass (x i) := by
  simp only [mass_linear, map_sum]
@[simp] lemma firstMoment_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) (a : Fin k) :
    firstMoment (∑ i ∈ t, x i) a = ∑ i ∈ t, firstMoment (x i) a := by
  exact map_sum (coefficientFunctional (k := k) (fun γ => γ a)) x t
@[simp] lemma secondMoment_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) (a b : Fin k) :
    secondMoment (∑ i ∈ t, x i) a b = ∑ i ∈ t, secondMoment (x i) a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_sum]

end Algebra
end EuclideanRamsey

end

end OAI


