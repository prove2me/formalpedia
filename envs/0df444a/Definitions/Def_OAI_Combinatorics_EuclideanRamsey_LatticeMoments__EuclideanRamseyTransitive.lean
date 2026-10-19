-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
-- name    : OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:00:21.397628+00:00
-- url     : https://prove2.me/theorems/80c9cf4b-fa2c-4651-85ed-6fcc7f5ba241
-- title:
--   Moments of rational signed measures on $\mathbb{Z}^k$, jet ideals and the finite lattice identity
-- statement:
--   This file sets up the group algebra of the integer lattice and the moment functionals of its elements, and formulates the finite lattice identity.
--
--   Fix $k\in\mathbb{N}$. Let $\mathbb{Z}^k$ be the integer lattice, $\mathbb{Q}^k$ the rational vector space with standard basis $e_1,\dots,e_k$, and $\iota:\mathbb{Z}^k\to\mathbb{Q}^k$ the coordinatewise inclusion, an additive homomorphism. Let $\mathbb{Q}[\mathbb{Z}^k]$ be the group algebra of $\mathbb{Z}^k$ over $\mathbb{Q}$ (the ring of rational Laurent polynomials in $k$ variables). An element $\nu\in\mathbb{Q}[\mathbb{Z}^k]$ is a finitely supported function $\gamma\mapsto\nu_\gamma\in\mathbb{Q}$ on $\mathbb{Z}^k$, thought of as a rational signed measure on the lattice; multiplication is convolution, and $[\gamma]$ denotes the basis element at $\gamma$.
--
--   1. **Rational span of a sublattice.** For a subgroup $\Lambda\le\mathbb{Z}^k$, $W_\Lambda\subseteq\mathbb{Q}^k$ is the $\mathbb{Q}$-linear span of $\iota(\Lambda)$, and $\pi_\Lambda:\mathbb{Q}^k\to\mathbb{Q}^k/W_\Lambda$ is the quotient map.
--   2. **Matrix tensor and quotient tensor map.** For a rational $k\times k$ matrix $C$, $\hat C=\sum_{a,b=1}^{k}C_{ab}\,e_a\otimes e_b\in\mathbb{Q}^k\otimes_{\mathbb{Q}}\mathbb{Q}^k$. The quotient tensor map of $\Lambda$ is the $\mathbb{Q}$-linear map $\pi_\Lambda\otimes\pi_\Lambda:\mathbb{Q}^k\otimes_{\mathbb{Q}}\mathbb{Q}^k\to(\mathbb{Q}^k/W_\Lambda)\otimes_{\mathbb{Q}}(\mathbb{Q}^k/W_\Lambda)$.
--   3. **Moments.** For $\nu\in\mathbb{Q}[\mathbb{Z}^k]$ and indices $a,b\in\{1,\dots,k\}$,
--   $$\operatorname{mass}(\nu)=\sum_{\gamma}\nu_\gamma,\qquad M_a(\nu)=\sum_{\gamma}\nu_\gamma\,\gamma_a,\qquad M_{ab}(\nu)=\sum_{\gamma}\nu_\gamma\,\gamma_a\gamma_b .$$
--   4. **Coset pushforward.** For a subgroup $\Lambda\le\mathbb{Z}^k$ with quotient map $q_\Lambda:\mathbb{Z}^k\to\mathbb{Z}^k/\Lambda$, $(q_\Lambda)_*\nu$ is the finitely supported function on $\mathbb{Z}^k/\Lambda$ whose value at a coset $c$ is $\sum_{\gamma\in c}\nu_\gamma$.
--   5. **Finite lattice identity.** The proposition: for all $k\ge1$ and $s\ge1$, all subgroups $\Lambda_1,\dots,\Lambda_s\le\mathbb{Z}^k$ and every symmetric rational $k\times k$ matrix $C$ with $(\pi_{\Lambda_i}\otimes\pi_{\Lambda_i})(\hat C)=0$ for every $i$, there exists $\nu\in\mathbb{Q}[\mathbb{Z}^k]$ such that $(q_{\Lambda_i})_*\nu=0$ for every $i$ (the weights of $\nu$ sum to $0$ on every coset of every $\Lambda_i$), $\operatorname{mass}(\nu)=0$, $M_a(\nu)=0$ for all $a$, and $M_{ab}(\nu)=C_{ab}$ for all $a,b$.
--   6. **Augmentation and moment calculus.** The augmentation $\operatorname{aug}:\mathbb{Q}[\mathbb{Z}^k]\to\mathbb{Q}$ is the $\mathbb{Q}$-algebra homomorphism with $\operatorname{aug}([\gamma])=1$ for every $\gamma$; it coincides with the mass, and its kernel is the augmentation ideal. For $g:\mathbb{Z}^k\to\mathbb{Q}$ the coefficient functional is the $\mathbb{Q}$-linear map $\nu\mapsto\sum_\gamma\nu_\gamma\,g(\gamma)$; mass and moments are instances of it. The file records that $\mathbb{Q}[\mathbb{Z}^k]$ is a Noetherian ring, that mass and moments are $\mathbb{Q}$-linear (with the corresponding rules for sums, finite sums, differences, scalar multiples, single basis elements, $0$ and $1$), that $\operatorname{mass}(xy)=\operatorname{mass}(x)\operatorname{mass}(y)$, and the product rules
--   $$M_a(xy)=\operatorname{mass}(x)M_a(y)+M_a(x)\operatorname{mass}(y),$$
--   $$M_{ab}(xy)=\operatorname{mass}(x)M_{ab}(y)+M_{ab}(x)\operatorname{mass}(y)+M_a(x)M_b(y)+M_b(x)M_a(y).$$
--   7. **Jet ideals.** $J_1=\{x:\operatorname{mass}(x)=0\text{ and }M_a(x)=0\text{ for all }a\}$ and $J_2=\{x\in J_1:M_{ab}(x)=0\text{ for all }a,b\}$; by the product rules these are ideals of $\mathbb{Q}[\mathbb{Z}^k]$.
--   8. **Quadratic stencil.** For a rational $k\times k$ matrix $C$ and $l_1,\dots,l_k\in\mathbb{Q}[\mathbb{Z}^k]$, $Q_C(l)=\tfrac12\sum_{a,b=1}^{k}C_{ab}\,l_al_b$.
--
--   The finite lattice identity is the discrete core of the passage from the tensor criterion to signed measures: it produces a finitely supported rational measure on the lattice with vanishing moments of order $0$ and $1$ and prescribed second moments that is balanced on the cosets of finitely many sublattices. The quadratic stencil is the basic way of realizing prescribed second moments: if each $l_a$ has mass $0$ and $M_b(l_a)=1$ for $a=b$ and $0$ otherwise, then by the product rules $Q_C(l)$ has mass $0$, first moments $0$ and second moments $C_{ab}$ whenever $C$ is symmetric. This file only formulates the finite lattice identity; it is established as a separate theorem.
--
--   **Formalization Note** `Lattice k` is `Fin k → ℤ`, `RationalSpace k` is `Fin k → ℚ` and `LatticeRing k` is `AddMonoidAlgebra ℚ (Lattice k)`; indices range over `Fin k`. The definitions are `rationalize` (the map $\iota$), `latticeSpan`, `matrixTensor`, `quotientTensor` (a `TensorProduct.map` of the quotient maps `mkQ`), `mass`, `firstMoment`, `secondMoment` (sums over `ν.coeff`), `cosetPushforward` (`Finsupp.mapDomain` along `QuotientAddGroup.mk'`), `FiniteLatticeIdentity : Prop`, the instance `latticeNoetherian`, `augmentation` (lift of the trivial character), `augmentationIdeal`, `coefficientFunctional`, the ideals `jetOne` and `jetTwo`, and `quadraticStencil`. The moment calculus consists of lemmas such as `augmentation_eq_mass`, `mass_linear`, `secondMoment_linear`, `mass_mul`, `firstMoment_mul`, `secondMoment_mul` and the simp lemmas for sums, differences and scalar multiples.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive

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
abbrev RationalSpace (k : ℕ) := Fin k → ℚ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)

def rationalize {k : ℕ} : Lattice k →+ RationalSpace k where
  toFun γ := fun j => (γ j : ℚ)
  map_zero' := by ext; simp
  map_add' γ δ := by ext; simp

def latticeSpan {k : ℕ} (Λ : AddSubgroup (Lattice k)) : Submodule ℚ (RationalSpace k) :=
  Submodule.span ℚ (rationalize '' (Λ : Set (Lattice k)))

def matrixTensor {k : ℕ} (C : Matrix (Fin k) (Fin k) ℚ) :
    RationalSpace k ⊗[ℚ] RationalSpace k :=
  ∑ a, ∑ b, C a b • ((Pi.single a (1 : ℚ)) ⊗ₜ[ℚ] (Pi.single b (1 : ℚ)))

def quotientTensor {k : ℕ} (Λ : AddSubgroup (Lattice k)) :=
  TensorProduct.map (latticeSpan Λ).mkQ (latticeSpan Λ).mkQ

def mass {k : ℕ} (ν : LatticeRing k) : ℚ := ν.coeff.sum fun _ q => q

def firstMoment {k : ℕ} (ν : LatticeRing k) (a : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a

def secondMoment {k : ℕ} (ν : LatticeRing k) (a b : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a * γ b

def cosetPushforward {k : ℕ} (Λ : AddSubgroup (Lattice k)) (ν : LatticeRing k) :
    (Lattice k ⧸ Λ) →₀ ℚ := Finsupp.mapDomain (QuotientAddGroup.mk' Λ) ν.coeff

def FiniteLatticeIdentity : Prop :=
  ∀ (k s : ℕ), 1 ≤ k → 1 ≤ s →
    ∀ (Λ : Fin s → AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ),
      C.IsSymm → (∀ i, quotientTensor (Λ i) (matrixTensor C) = 0) →
      ∃ ν : LatticeRing k,
        (∀ i, cosetPushforward (Λ i) ν = 0) ∧ mass ν = 0 ∧
        (∀ a, firstMoment ν a = 0) ∧ (∀ a b, secondMoment ν a b = C a b)

section Algebra
variable {k : ℕ}

instance latticeNoetherian : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)

def augmentation : LatticeRing k →ₐ[ℚ] ℚ :=
  AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

def augmentationIdeal : Ideal (LatticeRing k) := RingHom.ker augmentation

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

lemma firstMoment_mul (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x*y) a = mass x * firstMoment y a + firstMoment x a * mass y := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add]; ring
    | add y z hy hz => simp only [mul_add, firstMoment_add,  mass_add, hy, hz]; ring
    | smul r y hy => simp only [mul_smul_comm, firstMoment_smul,  mass_smul, hy]; ring
  | add x z hx hz => simp only [add_mul, firstMoment_add,  mass_add, hx, hz]; ring
  | smul r x hx => simp only [smul_mul_assoc, firstMoment_smul,  mass_smul, hx]; ring

lemma secondMoment_mul (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x*y) a b = mass x * secondMoment y a b + secondMoment x a b * mass y +
      firstMoment x a * firstMoment y b + firstMoment x b * firstMoment y a := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add, add_mul]; ring
    | add y z hy hz => simp only [mul_add, firstMoment_add, secondMoment_add, mass_add, hy, hz]; ring
    | smul r y hy => simp only [mul_smul_comm, firstMoment_smul, secondMoment_smul, mass_smul, hy]; ring
  | add x z hx hz => simp only [add_mul, firstMoment_add, secondMoment_add, mass_add, hx, hz]; ring
  | smul r x hx => simp only [smul_mul_assoc, firstMoment_smul, secondMoment_smul, mass_smul, hx]; ring

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

def jetOne : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ ∀ a, firstMoment x a = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp [hx.1, hx.2, hy.1, hy.2]
  smul_mem' r x hx := by
    change mass (r*x) = 0 ∧ ∀ a, firstMoment (r*x) a = 0
    simp [firstMoment_mul, hx.1, hx.2]

def jetTwo : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  smul_mem' r x hx := by
    change mass (r*x) = 0 ∧ (∀ a, firstMoment (r*x) a = 0) ∧ ∀ a b, secondMoment (r*x) a b = 0
    simp [firstMoment_mul, secondMoment_mul, hx.1, hx.2.1, hx.2.2]

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

def quadraticStencil (C : Matrix (Fin k) (Fin k) ℚ) (l : Fin k → LatticeRing k) : LatticeRing k :=
  (1/2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)

end Algebra
end EuclideanRamsey

end

end OAI


