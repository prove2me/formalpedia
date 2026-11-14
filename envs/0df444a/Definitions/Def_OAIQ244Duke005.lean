-- Prove2me | Definitions.Def_OAIQ244Duke005
-- name    : OAIQ244Duke005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:12:55.4387+00:00
-- url     : https://prove2.me/theorems/f81839d3-9f72-4a0c-bfa2-624abfdb8aba
-- title:
--   Definitions bundle OAIQ244Duke005 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 225 declarations of OpenAI's Lean: 88 definitions, 1 inductive type or structure, 6 instances and 130 theorems. The definitions and types are `ClassFormation.ProfiniteIntegerPrimeProduct`, `ClassFormation.abelianizationPreimageSubgroup`, `CyclicCohomology.BinaryCoefficientFamily`, `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom`, `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex`, `CyclicCohomology.ProfiniteCohomology.Herbrand.moduleCatRangeEquivOfConjugate`, `CyclicCohomology.ProfiniteCohomology.Herbrand.mulEquivRightRegularFunctionOfAddEquiv`, `CyclicCohomology.ProfiniteCohomology.Herbrand.multiplicativeMulDistribMulActionOfDistribMulAction`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicChainMap`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicHomologyIsoEven`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicHomologyIsoOdd`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicScIsoEven`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicScIsoOdd`, `CyclicCohomology.ProfiniteCohomology.Herbrand.periodicShortComplex`, `CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularCyclicIndex`, `CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularCyclicPartialProduct`, `CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularCyclicPrimitive`, `CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularFunctionMulDistribMulAction`, `CyclicCohomology.ProfiniteCohomology.Herbrand.subCompNormMap`, `CyclicCohomology.averagedLatticeMatrix`, `CyclicCohomology.averagedLatticeVector`, `CyclicCohomology.baseUnitToInvariantUnit`, `CyclicCohomology.binaryCoefficientFamilyAction`, `CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuot`, `CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv`, `CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotMk`, `CyclicCohomology.chosenNormalBasisPrincipalUnitSuccSubgroup`, `CyclicCohomology.chosenPermutationOrbitRepresentative`, `CyclicCohomology.chosenPermutationOrbitTransport`, `CyclicCohomology.completePermutationLatticeDistribMulAction`, `CyclicCohomology.coordinatePermutation`, `CyclicCohomology.finPartialProduct`, `CyclicCohomology.instFintypeSubtypeMemSubgroup_solutions`, `CyclicCohomology.instFintypeSubtypeMemSubgroup_solutions_1`, `CyclicCohomology.intCoordinatePermutation`, `CyclicCohomology.integerRingToFieldLinearMap`, `CyclicCohomology.invariantUnitToBaseUnit`, `CyclicCohomology.invariantsUnitsAddEquivBaseUnits`, `CyclicCohomology.invariantsUnitsEquivBaseUnits`, `CyclicCohomology.inverseCorrectionPartialSum` and 49 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_ClassFieldCandidate`, `AbstractClassFieldTheory_Reciprocity_Construction_RelativeNormDoubleCoset`, `AbstractClassFieldTheory_Reciprocity_Main`, `AbstractClassFieldTheory_Reciprocity_Reduction`, `AbstractClassFieldTheory_Reciprocity_Sylow`, `AlgebraicNumberTheory_Idele_IdealMap`, `AlgebraicNumberTheory_Idele_NormCore`, `AlgebraicNumberTheory_Idele_Topology`, `Cyclic_GaloisCohomology`, `Cyclic_Herbrand_HerbrandFiniteness`, `Cyclic_Herbrand_HerbrandLowDegree_Basic`, `Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct`, `Cyclic_Herbrand_HerbrandLowDegree_Cardinality`, `Cyclic_Herbrand_HerbrandLowDegree_Product`, `Cyclic_Herbrand_HerbrandLowDegree_TateComparison`, `Cyclic_Herbrand_Induced`, `Cyclic_Herbrand_NormalBasisLattice`, `Cyclic_Herbrand_Permutation_Lattice`, `Cyclic_Herbrand_Permutation_LatticeHerbrand`, `Cyclic_Herbrand_Permutation_Module`, `Cyclic_TateH0_Invariants`, `Cyclic_TateH0_NormImage`, `LocalField_DiscreteValuationField_Units`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_NonarchimedeanLocalField_PrincipalUnits`, `LocalField_NonarchimedeanLocalField_SeparableNormValuation`, `LocalField_Padic_ClosedAddSubgroup`, `PrimePackets_PacketMoments`, `ProfiniteIntegers_ProfiniteIntegerPrimeProduct`, `ProfiniteIntegers_ProfiniteIntegerUnits`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke021`, `OAIQ244Duke022`, `OAIQ244Duke023` and `OAIQ244Duke024`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.WithTopology

section
-- module Solutions.OAIQ244_DUKE.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_ClassFieldCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A finite class-field candidate from a norm-open subgroup

This file isolates the source-producing part of finite-classification surjectivity.
An open subgroup `H ≤ A_K` contains an actual finite Galois
norm subgroup.  Modulo that norm subgroup, `H` gives a concrete subgroup.
Transporting this subgroup to the additive abelianization and pulling it
back along `Q → Qᵃᵇ` gives a subgroup of the actual finite Galois quotient
which contains its commutator.  The finite Galois correspondence then cuts
out an actual finite abelian intermediate extension.

The equivalence used for the transport is an explicit argument of the
construction. A later specialization supplies it from finite reciprocity for
the reciprocity map.  No existence statement, norm-kernel equality, or
classification conclusion depending on that specialization is
asserted here.
-/

noncomputable section

namespace ClassFormation

open scoped commutatorElement

/-! ## The finite level beneath an open norm-topology subgroup -/

/-! ## From a subgroup above the commutator to an abelian field -/

/-- Pull a subgroup of an abelianization back to the original finite
Galois group. -/
def abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    Subgroup Q :=
  T.comap (Abelianization.of : Q →* Abelianization Q)

/-- Every such pullback contains the commutator subgroup. -/
theorem commutator_le_abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    commutator Q ≤ abelianizationPreimageSubgroup T := by
  intro q hq
  change Abelianization.of q ∈ T
  have hk : q ∈
      MonoidHom.ker (Abelianization.of : Q →* Abelianization Q) :=
    Abelianization.commutator_subset_ker
      (Abelianization.of : Q →* Abelianization Q) hq
  rw [MonoidHom.mem_ker.mp hk]
  exact T.one_mem

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_RelativeNormDoubleCoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

/-!
# The abstract reciprocity construction: the double-coset decomposition of a relative norm

The norm calculation in the proof of transfer--norm naturality partitions
the left cosets for an extension by the orbits of an intermediate subgroup.
This file constructs that partition from Mathlib's class-formula equivalence
and reindexes the actual relative norm along it.
-/

noncomputable section

open scoped BigOperators

open MulAction

/-- The class-formula inverse for an arbitrary chosen representative of
each orbit.  This form is used in transfer--norm naturality to choose the norm
representative `t⁻¹` attached to a transfer representative `t`. -/
@[simp]
theorem chosenOrbitClassEquiv_symm_apply
    {M : Type*} {X : Type*} [Group M] [MulAction M X]
    {φ : Quotient (orbitRel M X) → X}
    (hφ : Function.LeftInverse Quotient.mk'' φ)
    (q : Quotient (orbitRel M X))
    (r : M ⧸ stabilizer M (φ q)) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' M X hφ).symm
        ⟨q, r⟩ = r.out • φ q := by
  change (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm r :
      orbit M (φ q)) : X) = _
  refine Quotient.inductionOn' r ?_
  intro m
  calc
    (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm
        (QuotientGroup.mk m) : orbit M (φ q)) : X) = m • φ q :=
      MulAction.orbitEquivQuotientStabilizer_symm_apply M (φ q) m
    _ = (QuotientGroup.mk m).out • φ q := by
      symm
      simpa only [MulAction.ofQuotientStabilizer_mk] using
        congrArg (MulAction.ofQuotientStabilizer M (φ q))
          (QuotientGroup.out_eq' (QuotientGroup.mk m))

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

/-!
# The abstract reciprocity theorem: actual reduction maps

This file isolates the field- and quotient-theoretic content of the three
reductions.  In particular, the Sylow reduction uses an
intermediate field which need not be normal over the base.  We therefore
construct its norm map without a normality assumption on the intermediate
extension.

The reciprocity homomorphisms themselves belong to the finite reciprocity equivalence.  The
lemmas below only construct the actual arrows and prove the algebraic diagram
chases which will be applied to those homomorphisms.
-/

noncomputable section

universe u

section Representation

/-- The diagram chase used twice in the first reduction.  The
middle vertical arrow is surjective when the two outside vertical arrows
are surjective, the top-right arrow is surjective, and the bottom row is
exact. -/
theorem abstractReciprocity_surjective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) :
    Function.Surjective r := by
  intro b
  obtain ⟨q₁, hq₁⟩ := hr₁ (pB b)
  obtain ⟨q, hq⟩ := hpQ q₁
  have hzero : pB (b - r q) = 0 := by
    calc
      pB (b - r q) = pB b - pB (r q) := map_sub pB b (r q)
      _ = pB b - r₁ (pQ q) := by rw [hright q]
      _ = pB b - r₁ q₁ := by rw [hq]
      _ = pB b - pB b := by rw [hq₁]
      _ = 0 := sub_self _
  obtain ⟨b₀, hb₀⟩ := (hexact (b - r q)).mp hzero
  obtain ⟨q₀, hq₀⟩ := hr₀ b₀
  refine ⟨iQ q₀ + q, ?_⟩
  calc
    r (iQ q₀ + q) = r (iQ q₀) + r q := map_add r _ _
    _ = iB (r₀ q₀) + r q := by rw [hleft q₀]
    _ = iB b₀ + r q := by rw [hq₀]
    _ = (b - r q) + r q := by rw [hb₀]
    _ = b := sub_add_cancel b (r q)

/-- The diagram chase in the third reduction.  If both outside
reciprocity arrows are bijective and the first lower arrow is injective,
then the middle reciprocity arrow is bijective. -/
theorem abstractReciprocity_bijective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) :
    Function.Bijective r := by
  refine ⟨?_, abstractReciprocity_surjective_of_exact_diagram
    iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hpzero : pB (r q) = 0 := by rw [hq, map_zero]
  have hr₁zero : r₁ (pQ q) = 0 := by
    rw [← hright q]
    exact hpzero
  have hpQzero : pQ q = 0 := by
    apply hr₁.1
    simpa using hr₁zero
  obtain ⟨q₀, hq₀⟩ := (hexactQ q).mp hpQzero
  have hiBzero : iB (r₀ q₀) = 0 := by
    calc
      iB (r₀ q₀) = r (iQ q₀) := (hleft q₀).symm
      _ = r q := by rw [hq₀]
      _ = 0 := hq
  have hr₀zero : r₀ q₀ = 0 := by
    apply hiB
    simpa using hiBzero
  have hq₀zero : q₀ = 0 := by
    apply hr₀.1
    simpa using hr₀zero
  rw [← hq₀, hq₀zero, map_zero]

/-- Every additive homomorphism from a group into an abelian group kills
the commutator subgroup.  This is the automatic inclusion in the kernel
statement of the first reduction. -/
theorem abstractReciprocity_commutator_mem_kernel
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) :
    r (Additive.ofMul q) = 0 := by
  let rMul : Q →* Multiplicative B :=
    { toFun := fun x => Multiplicative.ofAdd (r (Additive.ofMul x))
      map_one' := r.map_zero
      map_mul' := r.map_add }
  have hker : q ∈ rMul.ker :=
    Abelianization.commutator_subset_ker rMul hq
  change Multiplicative.ofAdd (r (Additive.ofMul q)) = 1 at hker
  exact Multiplicative.ofAdd.injective (by simpa using hker)

end Representation

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Sylow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

/-!
# The abstract reciprocity theorem: the Sylow step in the first reduction

This file formalizes the source-producing group-theoretic part of the
first reduction.  For a Sylow `p`-subgroup `P` of the actual
finite quotient `G(L/K)`, the already constructed fixed field `M = L^P`
is an actual (not necessarily Galois over `K`) intermediate field.  The
actual quotient `G(L/M)` is a `p`-group and hence solvable, while
`[M:K] = (G(L/K) : P)` is prime to `p`.

For an abelian group `B`, multiplication by `[M:K]` is therefore
surjective on every Sylow `p`-subgroup of `B`, without assuming that the
ambient group is finite.  Equivalently, that Sylow subgroup lies in the
image of the `[M:K]`-fold map.  In the abstract reciprocity theorem the ambient norm quotient is
only known at this point to have bounded exponent; its individual cyclic
subgroups are finite.  This avoids using the desired reciprocity
surjectivity to prove finiteness.  No reciprocity surjectivity or
the finite reciprocity equivalence comparison is assumed here.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-! ## The fixed field of a Sylow subgroup -/

/-! ## Sylow subgroups in a possibly infinite abelian target -/

/-- Let `S` be a Sylow `p`-subgroup of an abelian group `B`.  If
`n` is prime to `p`, then `S` lies in the range of the additive `n`-fold
map on `B`.

The proof follows the sentence literally: `S` has `p`-power
order, so the `n`-fold map is a bijection on `S`; a preimage in `S` is in
particular a preimage in `B`. -/
theorem sylowAddSubgroup_le_nsmul_range_of_coprime
    {B : Type*} [AddCommGroup B]
    {p n : ℕ} [Fact p.Prime]
    (S : Sylow p (Multiplicative B)) (hn : Nat.Coprime n p) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B) n).range := by
  intro x hx
  let xS : S := ⟨Multiplicative.ofAdd x, hx⟩
  let e : S ≃ S := S.isPGroup'.powEquiv hn.symm
  let yS : S := e.symm xS
  refine ⟨yS.1.toAdd, ?_⟩
  have hy : yS ^ n = xS := e.apply_symm_apply xS
  have hyval : yS.1 ^ n = xS.1 := congrArg Subtype.val hy
  simpa [xS] using congrArg Multiplicative.toAdd hyval

end FiniteGaloisSubextension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

/-!
# The abstract reciprocity theorem

This file assembles the three reductions.  The terminal
cyclic totally ramified calculation is proved in
`AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase`.
-/

noncomputable section

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
theorem abstractReciprocity_subgroup_card_lt_of_ne_top
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) (hS : S ≠ ⊤) :
    Nat.card S < Nat.card Q := by
  by_contra hlt
  have hsurj : Function.Surjective S.subtype :=
    (S.subtype_injective.bijective_of_nat_card_le (Nat.le_of_not_gt hlt)).2
  apply hS
  rw [eq_top_iff]
  intro q _
  obtain ⟨s, hs⟩ := hsurj q
  rw [← hs]
  exact s.property

/-- Quotienting a finite group by a nontrivial normal subgroup strictly
decreases its cardinality. -/
theorem abstractReciprocity_quotient_card_lt_of_ne_bot
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) [S.Normal]
    (hS : S ≠ ⊥) :
    Nat.card (Q ⧸ S) < Nat.card Q := by
  by_contra hlt
  have hinj : Function.Injective (QuotientGroup.mk' S) :=
    ((QuotientGroup.mk'_surjective S).bijective_of_nat_card_le
      (Nat.le_of_not_gt hlt)).1
  apply hS
  rw [← QuotientGroup.ker_mk' S]
  exact (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' S)).2 hinj

/-- A subgroup of a finite commutative group which contains every Sylow
subgroup is the whole group. -/
theorem abstractReciprocity_subgroup_eq_top_of_sylow_le
    {B : Type*} [CommGroup B] [Finite B]
    (H : Subgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p B),
      (P : Subgroup B) ≤ H) :
    H = ⊤ := by
  classical
  apply (Subgroup.index_eq_one (H := H)).1
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpdvd
  let : Fact p.Prime := ⟨hp⟩
  let quotientMap : B →* B ⧸ H := QuotientGroup.mk' H
  have hquotientMap : Function.Surjective quotientMap :=
    QuotientGroup.mk'_surjective H
  let Q : Sylow p (B ⧸ H) := default
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
    hquotientMap p Q
  have hmapBot : (P : Subgroup B).map quotientMap = ⊥ := by
    exact (Subgroup.map_eq_bot_iff (P : Subgroup B)).2 (by
      simpa [quotientMap, QuotientGroup.ker_mk'] using hSylow P)
  have hQBot : (Q : Subgroup (B ⧸ H)) = ⊥ := by
    have hco := congrArg (fun S : Sylow p (B ⧸ H) =>
      (S : Subgroup (B ⧸ H))) hP
    simpa [hmapBot] using hco.symm
  exact (Q.ne_bot_of_dvd_card hpdvd) hQBot

/-- If a commutative group has finite exponent and an additive subgroup
contains every Sylow subgroup, then it is the whole group.  Only the finite
cyclic subgroup generated by the element under consideration is made
finite; no finiteness of the ambient group is assumed. -/
theorem abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    {B : Type*} [AddCommGroup B]
    (d : ℕ) (hd : 0 < d) (hexponent : ∀ b : B, d • b = 0)
    (H : AddSubgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime]
      (P : Sylow p (Multiplicative B)),
      Subgroup.toAddSubgroup'
        (P : Subgroup (Multiplicative B)) ≤ H) :
    H = ⊤ := by
  apply AddSubgroup.toSubgroup.injective
  apply top_unique
  intro g _
  let b : B := g.toAdd
  have hgfinite : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, by
      apply Multiplicative.toAdd.injective
      simpa [b] using hexponent b⟩
  let C := Subgroup.zpowers g
  let : Fintype C :=
    Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hgfinite)
  let J : Subgroup C := H.toSubgroup.comap C.subtype
  have hJ : J = ⊤ := by
    apply abstractReciprocity_subgroup_eq_top_of_sylow_le J
    intro p _ Q x hx
    have hQp : IsPGroup p ((Q : Subgroup C).map C.subtype) :=
      Q.isPGroup'.map C.subtype
    obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
    have hxmap : (x : Multiplicative B) ∈
        (Q : Subgroup C).map C.subtype :=
      ⟨x, hx, rfl⟩
    exact hSylow P (hQP hxmap)
  let x : C := ⟨g, Subgroup.mem_zpowers g⟩
  have hxJ : x ∈ J := by rw [hJ]; exact Subgroup.mem_top x
  exact hxJ

/-!
# Abstract reciprocity, reciprocity naturality: the three naturality diagrams

Reciprocity naturality states three diagrams for the norm residue
symbol.  Before taking the inverse of reciprocity, their vertical arrows are
exactly the maps already constructed in norm--conjugation and transfer--norm naturality:

* restriction on Galois groups together with the relative norm;
* conjugation on both sides;
* transfer together with inclusion of fixed elements.

This file applies abelianization to the Galois arrows and combines each pair
of vertical arrows into one map between the products
`Additive G(L/K)ᵃᵇ × A_K/N_{L/K}A_L`.  The formulas on quotient
representatives are proved from the actual maps.  Finally, the abstract reciprocity theorem and
norm--conjugation and transfer--norm naturality turn those reciprocity squares into the three printed
commutative diagrams for the inverse norm-residue symbol.
-/

noncomputable section

/-- A commutative square of additive isomorphisms remains commutative after
replacing both horizontal isomorphisms by their inverses. -/
theorem normResidueNaturality_symm_naturality
    {Q B Q' B' : Type*}
    [AddCommGroup Q] [AddCommGroup B]
    [AddCommGroup Q'] [AddCommGroup B']
    (r : Q ≃+ B) (r' : Q' ≃+ B')
    (q : Q →+ Q') (b : B →+ B')
    (h : b.comp r.toAddMonoidHom =
      r'.toAddMonoidHom.comp q) :
    q.comp r.symm.toAddMonoidHom =
      r'.symm.toAddMonoidHom.comp b := by
  apply AddMonoidHom.ext
  intro x
  apply r'.injective
  change r' (q (r.symm x)) = r' (r'.symm (b x))
  rw [r'.apply_symm_apply]
  have hx := DFunLike.congr_fun h (r.symm x)
  change b (r (r.symm x)) = r' (q (r.symm x)) at hx
  rw [r.apply_symm_apply] at hx
  exact hx.symm

/-! ## The norm/restriction diagram -/

/-! ## The conjugation diagram -/

/-! ## The inclusion/transfer diagram -/

/-! ## The three norm-residue diagrams -/

end
end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_IdealMap
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The exponent of a local multiplicative element, normalized so that a
uniformizer has exponent one. -/
def localOrder (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (-WithZero.log (Valued.v (x : v.adicCompletion K))))
    fun x y => by
      apply Multiplicative.ext
      simp [WithZero.log_mul, add_comm]

@[simp]
theorem localOrder_apply (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd =
      -WithZero.log (Valued.v (x : v.adicCompletion K)) :=
  rfl

@[simp]
theorem localOrder_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd = 0 ↔
      x ∈ (v.adicCompletionIntegers K).units := by
  rw [localOrder_apply]
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  change -WithZero.log (Valued.v (x : v.adicCompletion K)) = 0 ↔
    Valued.v (x : v.adicCompletion K) = 1
  rw [neg_eq_zero]
  let z : ℤᵐ⁰ := Valued.v (x : v.adicCompletion K)
  have hz : z ≠ 0 := by
    dsimp [z]
    simp
  constructor
  · intro h
    have h' :
        WithZero.logEquiv (Units.mk0 z hz) =
          WithZero.logEquiv (1 : (ℤᵐ⁰)ˣ) := by
      simpa [WithZero.logEquiv_apply] using h
    have hu := (WithZero.logEquiv (G := ℤ)).injective h'
    simpa [z] using congrArg Units.val hu
  · intro h
    rw [h]
    rfl

/-- A chosen local element of prescribed normalized order. -/
def chosenLocalOrderSection (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (v.adicCompletion K)ˣ :=
  let x := Classical.choose
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v
      (WithZero.exp (-n)))
  Units.mk0 x (by
    intro hx
    have hval := Classical.choose_spec
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-n)))
    change Valued.v x = WithZero.exp (-n) at hval
    rw [hx, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm)

end FiniteIdeleGroup

/-- The group of nonzero fractional ideals of a number field. -/
abbrev FractionalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

namespace FractionalIdealGroup

/-- The fractional ideal represented by a finite prime. -/
def prime (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdealGroup K :=
  Units.mk0 (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

end FractionalIdealGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Low-degree Herbrand quotients

This reusable implementation supplies the low-degree cyclic cohomology used
by the class-formation and local class field theory layers.
-/

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]

omit [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- First-isomorphism cardinality source for finite exactness calculations:
the cardinality of the source of a group homomorphism is the product of the
cardinalities of its kernel and range. -/
theorem monoidHom_card_eq_card_ker_mul_card_range
    {X : Type uA} {Y : Type uB} [Group X] [Group Y] [Finite X] (f : X →* Y) :
    Nat.card X = Nat.card (MonoidHom.ker f) * Nat.card (MonoidHom.range f) := by
  rw [← (MonoidHom.ker f).card_mul_index,
    Subgroup.index_ker]

omit [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Cardinality source for one exact spot of a group-hom sequence.  If
`range f = ker g`, then the middle group has cardinality
`#range(f) * #range(g)`. -/
theorem monoidHom_card_eq_card_range_mul_card_range_of_exact
    {X : Type uA} {Y : Type uB} {Z : Type uC} [Group X] [Group Y] [Group Z]
    [Finite Y]
    (f : X →* Y) (g : Y →* Z)
    (hexact : MonoidHom.range f = MonoidHom.ker g) :
    Nat.card Y = Nat.card (MonoidHom.range f) * Nat.card (MonoidHom.range g) := by
  rw [monoidHom_card_eq_card_ker_mul_card_range g, ← hexact]

omit [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- If `H ≤ K`, viewing `H` as a subgroup of `K` does not change its
cardinality. -/
theorem card_subgroupOf_eq_card
    {X : Type uA} [Group X] [Finite X] {H K : Subgroup X} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The multiplicative induced module from the trivial subgroup, represented
as functions on `G` with the right-regular action. This is the concrete model
used in the low-degree Herbrand comparison. -/
@[reducible] def rightRegularFunctionMulDistribMulAction :
    MulDistribMulAction G (G → B) where
  smul g f := fun x => f (x * g)
  one_smul := by
    intro f
    change (fun x => f (x * 1)) = f
    funext x
    rw [mul_one]
  mul_smul := by
    intro g h f
    change (fun x => f (x * (g * h))) = fun x => f ((x * g) * h)
    funext x
    rw [mul_assoc]
  smul_mul := by
    intro g f h
    funext x
    rfl
  smul_one := by
    intro g
    funext x
    rfl

omit [Fintype G] [CommGroup C] [MulDistribMulAction G C] in
/-- The inverse of an equivariant multiplicative equivalence is equivariant. -/
theorem mulEquiv_symm_commutes_smul
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    ∀ (g : G) (b : B), e.symm (g • b) = g • e.symm b := by
  intro g b
  apply e.injective
  calc
    e (e.symm (g • b)) = g • b := e.apply_symm_apply (g • b)
    _ = g • e (e.symm b) := by rw [e.apply_symm_apply]
    _ = e (g • e.symm b) := (he g (e.symm b)).symm

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The partial primitive along the cyclic powers of `σ`.  This is the
candidate used to solve `b (x * σ) * (b x)⁻¹ = f x` on the right-regular
induced module. -/
def rightRegularCyclicPartialProduct (σ : G) (f : G → B) (i : ℕ) : B :=
  (Finset.range i).prod (fun k => f (σ ^ k))

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The canonical `ZMod |G|` index of a group element with respect to a chosen
cyclic generator. -/
noncomputable def rightRegularCyclicIndex
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : G) :
    ZMod (Fintype.card G) :=
  Classical.choose (IsCyclic.unique_zpow_zmod (a := σ) hgen x)

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- If a concrete `ZMod |G|` representative is known, the cyclic index chooser
returns it. -/
theorem rightRegularCyclicIndex_eq_of_repr
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {x : G} {m : ZMod (Fintype.card G)} (hm : x = σ ^ m.val) :
    rightRegularCyclicIndex (G := G) σ hgen x = m := by
  exact ((Classical.choose_spec (IsCyclic.unique_zpow_zmod (a := σ) hgen x)).2 m hm).symm

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The group-element-indexed primitive candidate obtained from the cyclic
partial products. -/
noncomputable def rightRegularCyclicPrimitive
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) : G → B :=
  fun x =>
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f
      (rightRegularCyclicIndex (G := G) σ hgen x).val

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- A distributive action on an additive group induces a multiplicative action
on its `Multiplicative` wrapper. -/
@[reducible] def multiplicativeMulDistribMulActionOfDistribMulAction
    (G : Type uG) (M : Type uA) [Group G] [AddCommGroup M]
    [DistribMulAction G M] :
    MulDistribMulAction G (Multiplicative M) where
  smul g m := Multiplicative.ofAdd (g • Multiplicative.toAdd m)
  one_smul := by
    intro m
    change Multiplicative.ofAdd (1 • Multiplicative.toAdd m) =
      Multiplicative.ofAdd (Multiplicative.toAdd m)
    rw [one_smul]
  mul_smul := by
    intro g h m
    change Multiplicative.ofAdd ((g * h) • Multiplicative.toAdd m) =
      Multiplicative.ofAdd (g • h • Multiplicative.toAdd m)
    rw [mul_smul]
  smul_mul := by
    intro g m n
    change Multiplicative.ofAdd (g • Multiplicative.toAdd (m * n)) =
      Multiplicative.ofAdd
        (g • Multiplicative.toAdd m + g • Multiplicative.toAdd n)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n from rfl]
    rw [smul_add]
  smul_one := by
    intro g
    change Multiplicative.ofAdd (g • (0 : M)) = Multiplicative.ofAdd (0 : M)
    rw [smul_zero]

omit [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Convert an additive equivalence with a function space into the
multiplicative right-regular function model used by the Herbrand quotient API. -/
def mulEquivRightRegularFunctionOfAddEquiv
    (G : Type uG) {M : Type uA} {D : Type uB}
    [AddCommGroup M] [AddCommGroup D] (e : M ≃+ (G → D)) :
    Multiplicative M ≃* (G → Multiplicative D) where
  toFun m := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd m) x)
  invFun f := Multiplicative.ofAdd (e.symm (fun x => Multiplicative.toAdd (f x)))
  left_inv := by
    intro m
    change Multiplicative.ofAdd
        (e.symm (e (Multiplicative.toAdd m))) =
      Multiplicative.ofAdd (Multiplicative.toAdd m)
    exact congrArg Multiplicative.ofAdd (e.left_inv (Multiplicative.toAdd m))
  right_inv := by
    intro f
    funext x
    change Multiplicative.ofAdd
        (e (e.symm (fun y : G => Multiplicative.toAdd (f y))) x) =
      Multiplicative.ofAdd (Multiplicative.toAdd (f x))
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun q : G → D => q x)
        (e.right_inv (fun y : G => Multiplicative.toAdd (f y))))
  map_mul' := by
    intro m n
    funext x
    change Multiplicative.ofAdd (e (Multiplicative.toAdd (m * n)) x) =
      Multiplicative.ofAdd
        (e (Multiplicative.toAdd m) x + e (Multiplicative.toAdd n) x)
    rw [show Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n from rfl]
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun q : G → D => q x)
        (e.map_add (Multiplicative.toAdd m) (Multiplicative.toAdd n)))

omit [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Equivariance of `mulEquivRightRegularFunctionOfAddEquiv`, assuming the
input additive equivalence is right-regular equivariant pointwise. -/
theorem mulEquivRightRegularFunctionOfAddEquiv_commutes
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g))
    (g : G) (m : Multiplicative M) (x : G) :
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    mulEquivRightRegularFunctionOfAddEquiv G e (g • m) x =
      mulEquivRightRegularFunctionOfAddEquiv G e m (x * g) := by
  change Multiplicative.ofAdd (e (g • Multiplicative.toAdd m) x) =
    Multiplicative.ofAdd (e (Multiplicative.toAdd m) (x * g))
  exact congrArg Multiplicative.ofAdd (he g (Multiplicative.toAdd m) x)

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_TateComparison
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Comparisons between arithmetic Herbrand quotient presentations and mathlib Tate cohomology. -/

open CategoryTheory

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

universe u w

theorem repExact_of_hom_exact {k G : Type u} [CommRing k] [Group G]
    (S : ShortComplex (Rep.{w} k G))
    (h : ∀ b : S.X₂, S.g.hom b = 0 → ∃ a : S.X₁, S.f.hom a = b) :
    S.Exact :=
  (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 h

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- An equivariant homomorphism of multiplicative `G`-modules, regarded as
the corresponding morphism between mathlib's additive `ℤ`-representations. -/
def equivariantRepHom (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.ofMulDistribMulAction G A ⟶ Rep.ofMulDistribMulAction G B :=
  Rep.ofHom <|
    (MonoidHom.toAdditive f).toIntLinearMap.intertwiningMap_of_isIntertwiningMap
      (Rep.ofMulDistribMulAction G A).ρ
      (Rep.ofMulDistribMulAction G B).ρ <| by
      intro g a
      apply Additive.ofMul.injective
      exact hf g a.toMul

omit [Fintype G] in
@[simp]
theorem equivariantRepHom_apply (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : Additive A) :
    equivariantRepHom f hf a = Additive.ofMul (f a.toMul) :=
  rfl

/-- The short complex of mathlib representations associated to two
equivariant multiplicative homomorphisms whose composite is trivial. -/
def equivariantShortComplex
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (equivariantRepHom i hi) (equivariantRepHom j hj) <| by
    apply Rep.hom_ext
    ext a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

omit [Fintype G] in
theorem equivariantShortComplex_shortExact
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) :
    (equivariantShortComplex i j hi hj hker).ShortExact := by
  refine
    { exact := repExact_of_hom_exact _ ?_
      mono_f := (Rep.mono_iff_injective _).2 ?_
      epi_g := (Rep.epi_iff_surjective _).2 ?_ }
  · intro b hb
    change Additive.ofMul (j b.toMul) = 0 at hb
    have hb' : j b.toMul = 1 := Additive.ofMul.injective hb
    rcases (hker b.toMul).1 hb' with ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    change Additive.ofMul (i a) = b
    apply Additive.toMul.injective
    exact ha
  · intro a a' h
    change Additive.ofMul (i a.toMul) = Additive.ofMul (i a'.toMul) at h
    apply Additive.toMul.injective
    apply hinj
    exact Additive.ofMul.injective h
  · intro c
    rcases hsurj c.toMul with ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    change Additive.ofMul (j b) = c
    apply Additive.toMul.injective
    exact hb

end

end CyclicCohomology.ProfiniteCohomology.Herbrand
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Cardinality
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Cardinality identity from the standard Tate exact sequence

For a short exact sequence of finite cyclic modules, this module applies
mathlib's homology long exact sequence to the standard two-periodic cyclic
complex.  The resulting cardinality identity is transported to the
arithmetic `H⁰` and `H⁻¹` presentations.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

variable {G A B C : Type}

section

variable [CommGroup G] [Fintype G]
variable [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

noncomputable def subCompNormMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ ⟶
      Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ where
  τ₁ := (equivariantRepHom f hf).toModuleCatHom
  τ₂ := (equivariantRepHom f hf).toModuleCatHom
  τ₃ := (equivariantRepHom f hf).toModuleCatHom
  comm₁₂ := by
    ext a
    change Additive A at a
    change
      Additive.ofMul ((σ • f a.toMul) / f a.toMul) =
        Additive.ofMul (f ((σ • a.toMul) / a.toMul))
    exact congrArg Additive.ofMul (by rw [map_div, hf])
  comm₂₃ := by
    ext a
    apply Additive.ofMul.injective
    simp [Rep.FiniteCyclicGroup.subCompNormHom, Rep.norm,
      Representation.norm, Rep.hom_comm_apply]

noncomputable def periodicChainMap
    (σ : G) (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ ⟶
      Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G B) σ where
  f _ := (equivariantRepHom f hf).toModuleCatHom
  comm' := by
    rintro i j ⟨rfl⟩
    by_cases hj : Even (j + 1)
    · simp [Rep.FiniteCyclicGroup.moduleCatChainComplex,
        HomologicalComplex.alternatingConst, hj]
      exact (subCompNormMap σ f hf).comm₂₃
    · simp [Rep.FiniteCyclicGroup.moduleCatChainComplex,
        HomologicalComplex.alternatingConst, hj]
      exact (subCompNormMap σ f hf).comm₁₂

noncomputable def periodicShortComplex
    (σ : G)
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (periodicChainMap σ i hi) (periodicChainMap σ j hj) <| by
    apply HomologicalComplex.hom_ext
    intro n
    ext a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

theorem periodicShortComplex_shortExact
    (σ : G)
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) :
    (periodicShortComplex σ i j hi hj hker).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  refine
    { exact := ?_
      mono_f := (ModuleCat.mono_iff_injective _).2 ?_
      epi_g := (ModuleCat.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    intro b hb
    change Additive.ofMul (j b.toMul) = 0 at hb
    have hb' : j b.toMul = 1 := Additive.ofMul.injective hb
    rcases (hker b.toMul).1 hb' with ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    exact ha
  · intro a a' ha
    apply Additive.toMul.injective
    apply hinj
    exact Additive.ofMul.injective ha
  · intro c
    rcases hsurj c.toMul with ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    exact hb

noncomputable def periodicScIsoEven
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H)
    {n : ℕ} [h₀ : NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).sc n ≅
      Rep.FiniteCyclicGroup.subCompNormHom M τ :=
  HomologicalComplex.alternatingConstScIsoEven
    (ModuleCat.of R M.V)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by simp)
    (by
      induction n generalizing h₀ with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n _ => simp)
    hn

noncomputable def periodicScIsoOdd
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H) {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).sc n ≅
      Rep.FiniteCyclicGroup.normHomCompSub M τ :=
  HomologicalComplex.alternatingConstScIsoOdd
    (ModuleCat.of R M.V)
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (by ext; simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm])
    (fun _ _ => ComplexShape.down_nat_odd_add)
    (by simp)
    (by rcases hn with ⟨m, rfl⟩; simp)
    hn

noncomputable def periodicHomologyIsoEven
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H)
    {n : ℕ} [NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).homology n ≅
      (Rep.FiniteCyclicGroup.subCompNormHom M τ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoEven M τ hn)

noncomputable def periodicHomologyIsoOdd
    {R H : Type} [CommRing R] [CommGroup H] [Fintype H]
    (M : Rep R H) (τ : H) {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex M τ).homology n ≅
      (Rep.FiniteCyclicGroup.normHomCompSub M τ).homology :=
  ShortComplex.homologyMapIso (periodicScIsoOdd M τ hn)

theorem periodicScIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    ShortComplex.homologyMap
          (periodicScIsoEven
            (Rep.ofMulDistribMulAction G A) σ hn).inv ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor
            (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
              (periodicChainMap σ f hf)) ≫
        ShortComplex.homologyMap
          (periodicScIsoEven
            (Rep.ofMulDistribMulAction G B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) := by
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1

theorem periodicHomologyIsoEven_naturality
    (σ : G) {n : ℕ} [NeZero n] (hn : Even n)
    (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    (periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ hn).inv ≫
        HomologicalComplex.homologyMap (periodicChainMap σ f hf) n ≫
        (periodicHomologyIsoEven
          (Rep.ofMulDistribMulAction G B) σ hn).hom =
      ShortComplex.homologyMap (subCompNormMap σ f hf) :=
  periodicScIsoEven_naturality σ hn f hf

/-- Conjugating a `ModuleCat ℤ` morphism by isomorphisms identifies the
ranges of the associated multiplicatively tagged homomorphisms. -/
noncomputable def moduleCatRangeEquivOfConjugate
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    MonoidHom.range f.hom.toAddMonoidHom.toMultiplicative ≃
      MonoidHom.range g.hom.toAddMonoidHom.toMultiplicative := by
  have hnat : f ≫ eY.hom = eX.hom ≫ g := by
    rw [← cancel_epi eX.inv]
    simpa only [Category.assoc, eX.inv_hom_id_assoc] using h
  have hinv : eX.inv ≫ f = g ≫ eY.inv := by
    rw [← cancel_mono eY.hom]
    simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id] using h
  refine
    { toFun := fun y => ⟨Multiplicative.ofAdd (eY.hom y.1.toAdd), ?_⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (eY.inv y.1.toAdd), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.hom x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change g (eX.hom x.toAdd) = eY.hom y.1.toAdd
    have hx' : f x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact (congrArg (fun k : X ⟶ Y' => k x.toAdd) hnat).symm
  · rcases y.2 with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd (eX.inv x.toAdd), ?_⟩
    apply Multiplicative.toAdd.injective
    change f (eX.inv x.toAdd) = eY.inv y.1.toAdd
    have hx' : g x.toAdd = y.1.toAdd :=
      congrArg Multiplicative.toAdd hx
    rw [← hx']
    exact congrArg (fun k : X' ⟶ Y => k x.toAdd) hinv
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.hom_inv_id_apply y.1.toAdd
  · intro y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact eY.inv_hom_id_apply y.1.toAdd

/-- Conjugate `ModuleCat ℤ` morphisms have ranges of the same cardinality
after multiplicatively tagging their underlying additive groups. -/
theorem moduleCatRangeCard_eq_of_conjugate
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) :
    Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) =
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) :=
  Nat.card_congr (moduleCatRangeEquivOfConjugate f g eX eY h)

/-- Function exactness of morphisms in `ModuleCat ℤ` gives multiplicative
exactness after tagging the underlying additive groups as multiplicative. -/
theorem mulExact_of_moduleCat_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) :
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative := by
  intro y
  constructor
  · intro hy
    change g y.toAdd = 0 at hy
    rcases (hexact y.toAdd).1 hy with ⟨x, hx⟩
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    apply Multiplicative.toAdd.injective
    exact hx
  · rintro ⟨x, rfl⟩
    change g (f x.toAdd) = 0
    exact (hexact (f x.toAdd)).2 ⟨x.toAdd, rfl⟩

/-- For an exact pair of `ModuleCat ℤ` morphisms with finite middle term,
the cardinality of the middle term is the product of the two range
cardinalities. -/
theorem moduleCat_card_eq_card_range_mul_card_range_of_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) [Finite Y] :
    Nat.card Y =
      Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) *
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative) := by
  exact
    monoidHom_card_eq_card_range_mul_card_range_of_exact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative
      (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

/-- Finiteness transports from the target to the source of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_source_of_moduleIso
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite Y] :
    Finite X := by
  let e' : X ≃ Y := ((forget (ModuleCat ℤ)).mapIso e).toEquiv
  exact Finite.of_injective e' e'.injective

/-- Finiteness transports from the source to the target of a
`ModuleCat ℤ` isomorphism. -/
theorem finite_target_of_moduleIso
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite X] :
    Finite Y := by
  let e' : Y ≃ X := ((forget (ModuleCat ℤ)).mapIso e.symm).toEquiv
  exact Finite.of_injective e' e'.injective

/-- A `ModuleCat ℤ` isomorphism with the additive form of a commutative
group identifies their cardinalities. -/
theorem moduleCat_card_eq_of_iso
    {X : ModuleCat.{0} ℤ} {T : Type} [CommGroup T]
    (e : X ≅ ModuleCat.of ℤ (Additive T)) :
    Nat.card X = Nat.card T :=
  Nat.card_congr ((forget (ModuleCat ℤ)).mapIso e).toEquiv

end

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Finiteness in the Herbrand exact hexagon

This file supplies the finiteness clause in Herbrand-quotient multiplicativity:
for a short exact sequence of modules over a finite cyclic group, if the Herbrand
quotients of any two terms are defined, then the quotient of the third term is
defined as well.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

universe uG uA

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- In an exact pair `X → Y → Z`, finiteness of `X` and `Z` forces
finiteness of `Y`. -/
theorem finite_middle_of_exact
    {X Y Z : Type}
    [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)
    [Finite X] [Finite Z] :
    Finite Y := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · let : Finite (MonoidHom.range f) :=
      Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    rw [← hexact]
    infer_instance
  · infer_instance

theorem finite_middle_of_moduleCat_exact
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g)
    [Finite X] [Finite Z] :
    Finite Y := by
  let fm : Multiplicative X →* Multiplicative Y :=
    f.hom.toAddMonoidHom.toMultiplicative
  let gm : Multiplicative Y →* Multiplicative Z :=
    g.hom.toAddMonoidHom.toMultiplicative
  exact finite_middle_of_exact
    (X := Multiplicative X) (Y := Multiplicative Y)
    (Z := Multiplicative Z) fm gm
    (mulExact_of_moduleCat_exact f g hexact).monoidHom_ker_eq.symm

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Induced
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative induced modules

This file supplies the multiplicative induced-module model used in the
Herbrand quotient calculation.  If `H ≤ G` acts on a commutative group `B`, then
`Ind_H^G B` is represented by the equivariant functions

`f : G → B`,  `f (h * x) = h • f x`.

The ambient group acts by right translation.  This convention is the one
used for the products of the local multiplicative groups above a place.
The basic equivariant-function model is supplied by `ProCGroups.InducedFunctions`;
this module adds the cyclic-coordinate and Herbrand calculations.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uB

variable {G : Type uG} {B : Type uB}

/-- A one-step cyclic rotation whose wrap-around coordinate is acted on by
`τ`. -/
def twistedFinRotate {K C : Type*} [Group K] [CommGroup C]
    [MulDistribMulAction K C] {n : ℕ} [NeZero n]
    (τ : K) (v : Fin n → C) (i : Fin n) : C :=
  if finRotate n i = 0 then τ • v 0
  else v (finRotate n i)

/-- Cancellation of all non-wrap-around factors in a twisted rotation. -/
theorem prod_twistedFinRotate_div
    {K C : Type*} [Group K] [CommGroup C]
    [MulDistribMulAction K C] {n : ℕ} [NeZero n]
    (τ : K) (v : Fin n → C) :
    (∏ i : Fin n, twistedFinRotate τ v i) *
        (∏ i : Fin n, v i)⁻¹ =
      τ • v 0 * (v 0)⁻¹ := by
  classical
  let u : Fin n → C :=
    fun j ↦ if j = 0 then τ • v 0 else v j
  have hrotate :
      (∏ i : Fin n, twistedFinRotate τ v i) =
        ∏ j : Fin n, u j := by
    exact Fintype.prod_equiv
      (finRotate n) (twistedFinRotate τ v) u
      (fun i ↦ rfl)
  let R : C :=
    ∏ j ∈ (Finset.univ.erase (0 : Fin n)), v j
  have hu :
      (∏ j : Fin n, u j) = (τ • v 0) * R := by
    rw [← Finset.mul_prod_erase Finset.univ u
      (Finset.mem_univ (0 : Fin n))]
    simp only [u, ite_eq_left, R]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hj0 : j ≠ 0 :=
      Finset.ne_of_mem_erase hj
    simp [hj0]
  have hv :
      (∏ j : Fin n, v j) = v 0 * R := by
    rw [← Finset.mul_prod_erase Finset.univ v
      (Finset.mem_univ (0 : Fin n))]
  rw [hrotate, hu, hv]
  simp only [mul_inv_rev]
  calc
    (τ • v 0) * R * (R⁻¹ * (v 0)⁻¹) =
        (τ • v 0) * (v 0)⁻¹ *
          (R * R⁻¹) := by ac_rfl
    _ = τ • v 0 * (v 0)⁻¹ := by simp

/-- Multiplication by the cyclic generator advances `finRotate`, with the
last coordinate wrapping to the full-period power. -/
theorem pow_mul_eq_pow_finRotate
    {X : Type*} [Monoid X] {n : ℕ} [NeZero n]
    (a : X) (i : Fin n) :
    a ^ i.1 * a =
      if finRotate n i = 0 then a ^ n
      else a ^ (finRotate n i).1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        simp [pow_succ]
      · have hil : i.1 < n :=
          Fin.val_lt_last hi
        rw [finRotate_of_lt hil]
        simp [pow_succ]

/-- Partial product of a finite vector. -/
def finPartialProduct {C : Type*} [CommMonoid C]
    {n : ℕ} (v : Fin n → C) (k : ℕ) : C :=
  (Finset.range k).prod fun i ↦
    if hi : i < n then v ⟨i, hi⟩ else 1

@[simp]
theorem finPartialProduct_zero
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) :
    finPartialProduct v 0 = 1 := by
  simp [finPartialProduct]

theorem finPartialProduct_succ
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) (i : Fin n) :
    finPartialProduct v (i.1 + 1) =
      finPartialProduct v i.1 * v i := by
  simp [finPartialProduct,
    Finset.prod_range_succ, i.2]

theorem finPartialProduct_full
    {C : Type*} [CommMonoid C] {n : ℕ}
    (v : Fin n → C) :
    finPartialProduct v n = ∏ i : Fin n, v i := by
  simpa [finPartialProduct] using
    (Finset.prod_fin_eq_prod_range v).symm

/-- A split homomorphism induces an equivalence of quotients when it
identifies the selected subgroups and its remaining kernel lies in the
source subgroup. -/
noncomputable def quotientMulEquivOfSplit
    {X Y : Type*} [CommGroup X] [CommGroup Y]
    (N : Subgroup X) (M : Subgroup Y)
    (f : X →* Y) (s : Y →* X)
    (hfs : ∀ y : Y, f (s y) = y)
    (hfN : ∀ x : X, x ∈ N → f x ∈ M)
    (hsM : ∀ y : Y, y ∈ M → s y ∈ N)
    (hker : ∀ x : X, f x = 1 → x ∈ N) :
    X ⧸ N ≃* Y ⧸ M := by
  let qf : (X ⧸ N) →* (Y ⧸ M) :=
    QuotientGroup.map N M f (fun x hx ↦ hfN x hx)
  let qs : (Y ⧸ M) →* (X ⧸ N) :=
    QuotientGroup.map M N s (fun y hy ↦ hsM y hy)
  refine MonoidHom.toMulEquiv qf qs ?_ ?_
  · apply QuotientGroup.monoidHom_ext
    ext x
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply hker
    simp [hfs]
  · apply QuotientGroup.monoidHom_ext
    ext y
    apply QuotientGroup.eq_iff_div_mem.mpr
    simp [hfs]

section InducedHerbrandH0

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

local instance instFintypeSubtypeMemSubgroup_solutions : Fintype H := Fintype.ofFinite H

end InducedHerbrandH0

section InducedHerbrandHMinusOne

variable [CommGroup G] [Fintype G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

local instance instFintypeSubtypeMemSubgroup_solutions_1 : Fintype H := Fintype.ofFinite H

local instance instNeZeroNatIndex_solutions : NeZero H.index := ⟨by
  rw [H.index_eq_card]
  exact Nat.card_pos.ne'⟩

end InducedHerbrandHMinusOne

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Product
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of products

This file proves that multiplicative Tate `H⁰` and `H⁻¹` commute with
dependent products, giving the product step for low-degree Herbrand quotients.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

/-- The pointwise product of a family of subgroups. -/
def piSubgroup (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    Subgroup (∀ i, A i) where
  carrier := {x | ∀ i, x i ∈ N i}
  one_mem' i := (N i).one_mem
  mul_mem' hx hy i := (N i).mul_mem (hx i) (hy i)
  inv_mem' hx i := (N i).inv_mem (hx i)

@[simp]
theorem mem_piSubgroup_iff
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i))
    (x : ∀ i, A i) :
    x ∈ piSubgroup ι A N ↔
      ∀ i, x i ∈ N i :=
  Iff.rfl

/-- The componentwise quotient map. -/
noncomputable def piQuotientMap
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (∀ i, A i) →* ∀ i, A i ⧸ N i where
  toFun x i := QuotientGroup.mk' (N i) (x i)
  map_one' := by
    ext i
    exact (QuotientGroup.mk' (N i)).map_one
  map_mul' x y := by
    ext i
    exact (QuotientGroup.mk' (N i)).map_mul
      (x i) (y i)

@[simp]
theorem piQuotientMap_apply
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i))
    (x : ∀ i, A i) (i : ι) :
    piQuotientMap ι A N x i =
      QuotientGroup.mk' (N i) (x i) :=
  rfl

theorem ker_piQuotientMap
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (piQuotientMap ι A N).ker =
      piSubgroup ι A N := by
  ext x
  constructor
  · intro hx i
    have hmap :
        piQuotientMap ι A N x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hi : QuotientGroup.mk' (N i) (x i) = 1 :=
      (piQuotientMap_apply ι A N x i).symm.trans (congrFun hmap i)
    exact
      (QuotientGroup.eq_one_iff
        (N := N i) (x := x i)).mp hi
  · intro hx
    exact MonoidHom.mem_ker.mpr <| by
      ext i
      exact
        (QuotientGroup.eq_one_iff
          (N := N i) (x := x i)).mpr (hx i)

theorem piQuotientMap_surjective
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    Function.Surjective (piQuotientMap ι A N) := by
  intro y
  choose x hx using fun i =>
    QuotientGroup.mk'_surjective (N i) (y i)
  refine ⟨x, ?_⟩
  ext i
  exact hx i

/-- The quotient of a dependent product by the pointwise subgroup is the
dependent product of the quotients. -/
noncomputable def piQuotientEquiv
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (∀ i, A i) ⧸ piSubgroup ι A N ≃*
      ∀ i, A i ⧸ N i :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_piQuotientMap ι A N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (piQuotientMap ι A N)
      (piQuotientMap_surjective ι A N))

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Module
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of permutation lattices

This file supplies the abstract cohomology calculation for permutation
lattices.  It proves the value of the Herbrand quotient on the trivial
integer lattice, transports that calculation through Shapiro's lemma to
transitive permutation lattices, and multiplies over a finite family of
orbits.  It also records invariance under passage to a finite-index stable
subgroup.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uι

/-- The trivial multiplicative action on the additive group of integers,
written multiplicatively. -/
@[reducible]
def trivialIntMulDistribMulAction
    (G : Type uG) [Group G] :
    MulDistribMulAction G (Multiplicative ℤ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

section CanonicalPermutationFunctions

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι] [MulAction G ι]

/-- The contragredient action on integer-valued functions on a finite
`G`-set. -/
@[reducible]
def permutationFunctionMulDistribMulAction :
    MulDistribMulAction G (ι → Multiplicative ℤ) where
  smul g f i := f (g⁻¹ • i)
  one_smul f := by
    funext i
    change f ((1 : G)⁻¹ • i) = f i
    rw [inv_one, one_smul]
  mul_smul g h f := by
    funext i
    change f ((g * h)⁻¹ • i) =
      f (h⁻¹ • (g⁻¹ • i))
    rw [mul_inv_rev, mul_smul]
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- A chosen representative of the orbit containing `i`. -/
noncomputable def chosenPermutationOrbitRepresentative
    (i : ι) : ι :=
  Quotient.out
    (Quotient.mk'' i :
      MulAction.orbitRel.Quotient G ι)

omit [Fintype G] [Fintype ι] in
theorem chosenPermutationOrbitRepresentative_sameOrbit
    (i : ι) :
    i ∈ MulAction.orbit G
      (chosenPermutationOrbitRepresentative (G := G) i) := by
  rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
  exact
    (Quotient.out_eq'
      (Quotient.mk'' i :
        MulAction.orbitRel.Quotient G ι)).symm

/-- A chosen group element carrying the chosen representative of
the orbit of `i` to `i`. -/
noncomputable def chosenPermutationOrbitTransport
    (i : ι) : G :=
  Classical.choose
    (chosenPermutationOrbitRepresentative_sameOrbit
      (G := G) i)

omit [Fintype G] [Fintype ι] in
theorem chosenPermutationOrbitTransport_smul
    (i : ι) :
    chosenPermutationOrbitTransport (G := G) i •
        chosenPermutationOrbitRepresentative (G := G) i = i :=
  Classical.choose_spec
    (chosenPermutationOrbitRepresentative_sameOrbit
      (G := G) i)

/-- The stabilizer of the chosen representative of an orbit. -/
abbrev permutationOrbitStabilizer
    (ω : MulAction.orbitRel.Quotient G ι) :
    Subgroup G :=
  MulAction.stabilizer G ω.out

end CanonicalPermutationFunctions

section FiniteIndexStableSubgroup

variable {G : Type uG} {A : Type uA}
    [Group G] [CommGroup A]
    [MulDistribMulAction G A]

/-- Restriction of an action to a stable subgroup. -/
@[reducible]
def stableSubgroupMulDistribMulAction
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    MulDistribMulAction G B where
  smul g x := ⟨g • x.1, hstable g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul G x.1
  mul_smul g h x := by
    apply Subtype.ext
    exact mul_smul g h x.1
  smul_one g := by
    apply Subtype.ext
    exact MulDistribMulAction.smul_one g
  smul_mul g x y := by
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul
      g x.1 y.1

@[simp]
theorem stableSubgroup_smul_coe
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (g : G) (x : B) :
    letI :=
      stableSubgroupMulDistribMulAction
        B hstable
    ((g • x : B) : A) = g • (x : A) :=
  rfl

/-- The action induced on the quotient by a stable subgroup. -/
@[reducible]
def stableQuotientMulDistribMulAction
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    MulDistribMulAction G (A ⧸ B) where
  smul g q :=
    QuotientGroup.map B B
      (MulDistribMulAction.toMonoidHom A g)
      (fun _ hx ↦ hstable g _ hx) q
  one_smul q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change
      QuotientGroup.mk' B ((1 : G) • x) =
        QuotientGroup.mk' B x
    rw [one_smul]
  mul_smul g h q := by
    refine QuotientGroup.induction_on q ?_
    intro x
    change
      QuotientGroup.mk' B ((g * h) • x) =
        QuotientGroup.mk' B (g • h • x)
    rw [mul_smul]
  smul_one g :=
    map_one
      (QuotientGroup.map B B
        (MulDistribMulAction.toMonoidHom A g)
        (fun _ hx ↦ hstable g _ hx))
  smul_mul g q r :=
    map_mul
      (QuotientGroup.map B B
        (MulDistribMulAction.toMonoidHom A g)
        (fun _ hx ↦ hstable g _ hx))
      q r

@[simp]
theorem stableQuotient_smul_mk
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (g : G) (x : A) :
    letI :=
      stableQuotientMulDistribMulAction
        B hstable
    g • QuotientGroup.mk' B x =
      QuotientGroup.mk' B (g • x) :=
  rfl

/-- The inclusion of a stable subgroup is equivariant. -/
theorem stableSubgroup_subtype_equivariant
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    letI :=
      stableSubgroupMulDistribMulAction
        B hstable
    ∀ (g : G) (x : B),
      B.subtype (g • x) = g • B.subtype x := by
  let :=
    stableSubgroupMulDistribMulAction
      B hstable
  intro g x
  rfl

/-- The quotient map by a stable subgroup is equivariant. -/
theorem stableSubgroup_quotientMap_equivariant
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B) :
    letI :=
      stableQuotientMulDistribMulAction
        B hstable
    ∀ (g : G) (x : A),
      QuotientGroup.mk' B (g • x) =
        g • QuotientGroup.mk' B x := by
  let :=
    stableQuotientMulDistribMulAction
      B hstable
  intro g x
  rfl

/-- Exactness of the inclusion followed by the quotient map. -/
theorem stableSubgroup_quotientMap_exact
    (B : Subgroup A) :
    ∀ x : A,
      QuotientGroup.mk' B x = 1 ↔
        ∃ b : B, B.subtype b = x := by
  intro x
  constructor
  · intro hx
    have hxB :
        x ∈ B :=
      (QuotientGroup.eq_one_iff x).mp hx
    exact ⟨⟨x, hxB⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact
      (QuotientGroup.eq_one_iff b.1).mpr
        b.2

end FiniteIndexStableSubgroup

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Principal units

Defines the filtration `U^n = 1 + 𝓂^n`, proves its basic order properties, and
constructs the quotient of valuation-ring units by the first filtration step.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Algebra identity used to prove multiplicative closure of principal units. -/
lemma unit_mul_sub_one_eq (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    ((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
      ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) +
        ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1) := by
  simp only [Units.val_mul]
  ring

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-! ### Separatedness of the principal-unit filtration -/

/-! ### Maximal-ideal powers as local neighborhoods -/

/-- Every neighborhood of zero in the valuation integer ring contains a
sufficiently deep power of the maximal ideal. -/
theorem exists_maximalIdeal_pow_subset_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases (mem_nhds_subtype ((ValuativeRel.valuation K).integer : Set K)
      (0 : 𝒪[K]) s).1 hs with
    ⟨t, ht, hts⟩
  rcases (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp ht with
    ⟨γ, -, hγt⟩
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[K] with ⟨ϖ, hϖ⟩
  rcases exists_pow_lt₀
      (Valuation.integer.v_irreducible_lt_one (v := ValuativeRel.valuation K) hϖ)
      γ with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x hx
  apply hts
  apply hγt
  have hset := Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    (v := ValuativeRel.valuation K) hϖ N
  have hxset : x ∈ ((𝓂[K] ^ N : Ideal 𝒪[K]) : Set 𝒪[K]) := hx
  rw [hset] at hxset
  exact hxset.trans_lt hN

/-- Eventual form of `exists_maximalIdeal_pow_subset_nhds_zero`: all deeper
powers of the maximal ideal lie in a fixed zero-neighborhood. -/
theorem eventually_maximalIdeal_pow_subset_nhds_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : Set 𝒪[K])
    (hs : s ∈ nhds (0 : 𝒪[K])) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      ((𝓂[K] ^ m : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ s := by
  rcases exists_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  refine ⟨N, fun m hm x hx => hN ?_⟩
  exact Ideal.pow_le_pow_right hm hx

/-- Powers of an element of the maximal ideal tend to zero in the valuation
integer ring. -/
theorem tendsto_pow_succ_of_mem_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) :
    Tendsto (fun d : Nat => x ^ (d + 1)) atTop (nhds (0 : 𝒪[K])) := by
  rw [tendsto_def]
  intro s hs
  rcases eventually_maximalIdeal_pow_subset_nhds_zero K s hs with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with d hd
  exact hN (d + 1) (le_trans hd (Nat.le_succ d))
    (Ideal.pow_mem_pow hx (d + 1))

/-- The signed version used by finite geometric inverse corrections. -/
theorem tendsto_neg_pow_succ_of_mem_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {x : 𝒪[K]}
    (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) :
    Tendsto (fun d : Nat => (-x) ^ (d + 1)) atTop (nhds (0 : 𝒪[K])) :=
  tendsto_pow_succ_of_mem_maximalIdeal K ((𝓂[K] : Ideal 𝒪[K]).neg_mem hx)

/-! ### Finite correction products for complete lifting -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Units
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

universe u v

open scoped BigOperators

namespace DiscreteValuationField

/-- A generic antitone filtration by subgroups of a group.  No valued-field
semantics are asserted by this interface alone. -/
structure AntitoneSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each natural-number filtration level. -/
  subgroup : ℕ → Subgroup G
  /-- Higher filtration levels are contained in lower ones. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → subgroup n ≤ subgroup m

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The `n`-th principal-unit subgroup. -/
def principalUnitSubgroup (n : ℕ) : Subgroup G :=
  U.subgroup n

/-- Characterizes `x ∈ U.principalUnitSubgroup n` by the equivalent condition `x ∈ U.subgroup n`. -/
@[simp] theorem mem_principalUnitSubgroup_iff (n : ℕ) (x : G) :
    x ∈ U.principalUnitSubgroup n ↔ x ∈ U.subgroup n :=
  Iff.rfl

/-- Higher filtration levels are contained in lower levels. -/
theorem principalUnitSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    U.principalUnitSubgroup n ≤ U.principalUnitSubgroup m :=
  U.antitone h

/-- Establishes the membership statement `x ∈ U.principalUnitSubgroup m`. -/
theorem mem_of_mem_of_le {m n : ℕ} (h : m ≤ n) {x : G}
    (hx : x ∈ U.principalUnitSubgroup n) :
    x ∈ U.principalUnitSubgroup m :=
  U.principalUnitSubgroup_antitone h hx

/-- The natural map from a finer filtration quotient to a coarser filtration
quotient.  If `m ≤ n`, then `U^n ≤ U^m`, so quotienting by `U^n` maps to
quotienting by `U^m`. -/
def quotient_principalUnitSubgroup_mapOfLe {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    G ⧸ U.principalUnitSubgroup n →*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.map (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)

/--
The defining evaluation formula for `quotient_principalUnitSubgroup_mapOfLe` is
`U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) = QuotientGroup.mk x`.
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) =
      QuotientGroup.mk x :=
  rfl

/--
Establishes the identity `U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk'
(U.principalUnitSubgroup n) x) = QuotientGroup.mk' (U.principalUnitSubgroup m) x`.
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk'
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x :=
  rfl

/-- The class of `U^m` inside `G ⧸ U^n`.  For `m ≤ n`, this is the kernel of
the natural map `G ⧸ U^n →* G ⧸ U^m`. -/
def principalUnitSubgroupClassInQuotient (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal] :
    Subgroup (G ⧸ U.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
    (U.principalUnitSubgroup m)

/--
Characterizes `q ∈ U.principalUnitSubgroupClassInQuotient m n` by the equivalent condition `∃ x :
G, x ∈ U.principalUnitSubgroup m ∧ QuotientGroup.mk' (U.principalUnitSubgroup n) x = q`.
-/
theorem mem_principalUnitSubgroupClassInQuotient_iff
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (q : G ⧸ U.principalUnitSubgroup n) :
    q ∈ U.principalUnitSubgroupClassInQuotient m n ↔
      ∃ x : G, x ∈ U.principalUnitSubgroup m ∧
        QuotientGroup.mk' (U.principalUnitSubgroup n) x = q :=
  Iff.rfl

/--
Establishes the membership statement `QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
U.principalUnitSubgroupClassInQuotient m n`.
-/
theorem principalUnitSubgroupClassInQuotient_mk_mem
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal] {x : G}
    (hx : x ∈ U.principalUnitSubgroup m) :
    QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
      U.principalUnitSubgroupClassInQuotient m n :=
  Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (U.principalUnitSubgroup n)) hx

/-- The subquotient `U^m/U^n` of a principal-unit filtration.  Under
`m ≤ n`, antitonicity makes this the usual quotient of `U^m` by `U^n`. -/
def principalUnitSubquotient (m n : ℕ) : Type u :=
  U.principalUnitSubgroup m ⧸
    (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitSubquotient
m n)`.
-/
instance principalUnitSubquotientGroup
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    Group (U.principalUnitSubquotient m n) := by
  change Group
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  infer_instance

/-- Explicit access to the concrete quotient representation. -/
def principalUnitSubquotientConcreteEquiv
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) := by
  change
    (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m))
  exact MulEquiv.refl _

/-- The canonical class map `U^m → U^m/U^n`. -/
def principalUnitSubquotientMk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* U.principalUnitSubquotient m n := by
  change U.principalUnitSubgroup m →*
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  exact QuotientGroup.mk'
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m))

/--
Establishes the identity `U.principalUnitSubquotientConcreteEquiv m n
(U.principalUnitSubquotientMk m n x) = QuotientGroup.mk x`.
-/
@[simp]
theorem principalUnitSubquotientConcreteEquiv_mk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientConcreteEquiv m n
        (U.principalUnitSubquotientMk m n x) =
      QuotientGroup.mk x :=
  rfl

/-- Descend a homomorphism that kills `U^n` inside `U^m`. -/
def principalUnitSubquotientLift
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker) :
    U.principalUnitSubquotient m n →* H := by
  change
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m)) →* H
  exact QuotientGroup.lift
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)) f h

/--
Establishes the identity `U.principalUnitSubquotientLift m n f h (U.principalUnitSubquotientMk m n
x) = f x`.
-/
@[simp]
theorem principalUnitSubquotientLift_mk
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker)
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientLift m n f h
        (U.principalUnitSubquotientMk m n x) = f x :=
  rfl

/-- The map from `U^m` into `G/U^n`. -/
def principalUnitSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* G ⧸ U.principalUnitSubgroup n :=
  (QuotientGroup.mk' (U.principalUnitSubgroup n)).comp
    (U.principalUnitSubgroup m).subtype

/--
The defining evaluation formula for `principalUnitSubgroupToQuotient` is
`U.principalUnitSubgroupToQuotient hmn x = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
-/
@[simp] theorem principalUnitSubgroupToQuotient_apply
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubgroupToQuotient hmn x =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) :=
  rfl

/-- The kernel of `U^m → G/U^n` is `U^n` inside `U^m`. -/
theorem principalUnitSubgroupToQuotient_ker_eq
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).ker =
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [principalUnitSubgroupToQuotient_apply, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_one_iff (N := U.principalUnitSubgroup n) (x : G)

/-- The range of `U^m → G/U^n` is the class of `U^m` in `G/U^n`. -/
theorem principalUnitSubgroupToQuotient_range_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).range =
      U.principalUnitSubgroupClassInQuotient m n := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : G), x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The subquotient `U^m/U^n` as the class of `U^m` inside `G/U^n`. -/
noncomputable def principalUnitSubquotientEquivClassInQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (U.principalUnitSubquotientConcreteEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (U.principalUnitSubgroupToQuotient_ker_eq hmn).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        (U.principalUnitSubgroupToQuotient hmn)).trans
          (MulEquiv.subgroupCongr
            (U.principalUnitSubgroupToQuotient_range_eq_classInQuotient hmn))))

/--
Establishes the identity `((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
(U.principalUnitSubquotientMk m n x) : U.principalUnitSubgroupClassInQuotient m n) : G ⧸
U.principalUnitSubgroup n) = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
-/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    ((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
        (U.principalUnitSubquotientMk m n x) :
      U.principalUnitSubgroupClassInQuotient m n) :
      G ⧸ U.principalUnitSubgroup n) =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) := by
  simp [principalUnitSubquotientEquivClassInQuotientOfLe]
  rfl

/-- Level-change maps send the class of `U^l` in `G/U^n` into the class of
`U^l` in `G/U^m`, for `l ≤ m ≤ n`. -/
theorem quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
    {l m n : ℕ} (_hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    {q : G ⧸ U.principalUnitSubgroup n}
    (hq : q ∈ U.principalUnitSubgroupClassInQuotient l n) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn q ∈
      U.principalUnitSubgroupClassInQuotient l m := by
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l n q).1 hq with
    ⟨x, hx, hxq⟩
  rw [← hxq, U.quotient_principalUnitSubgroup_mapOfLe_apply_mk']
  exact U.principalUnitSubgroupClassInQuotient_mk_mem hx

/-- The level-change map restricted to principal-unit classes:
`U^l/U^n → U^l/U^m`, for `l ≤ m ≤ n`. -/
def principalUnitClassMapOfLe {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n →*
      U.principalUnitSubgroupClassInQuotient l m :=
  ((U.quotient_principalUnitSubgroup_mapOfLe hmn).domRestrict
      (U.principalUnitSubgroupClassInQuotient l n)).codRestrict
    (U.principalUnitSubgroupClassInQuotient l m)
    (by
      intro q
      exact U.quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
        hlm hmn q.property)

/--
The defining evaluation formula for `principalUnitClassMapOfLe` is `((U.principalUnitClassMapOfLe
hlm hmn q : U.principalUnitSubgroupClassInQuotient l m) : G ⧸ U.principalUnitSubgroup m) =
U.quotient_principalUnitSubgroup_mapOfLe hmn (q : G ⧸ U.principalUnitSubgroup n)`.
-/
@[simp] theorem principalUnitClassMapOfLe_apply {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : U.principalUnitSubgroupClassInQuotient l n) :
    ((U.principalUnitClassMapOfLe hlm hmn q :
      U.principalUnitSubgroupClassInQuotient l m) :
      G ⧸ U.principalUnitSubgroup m) =
      U.quotient_principalUnitSubgroup_mapOfLe hmn
        (q : G ⧸ U.principalUnitSubgroup n) :=
  rfl

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormCore
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The absolute norm of an idele

This file constructs the homomorphism `𝓝 : I_K → ℝ₊ˣ`. At a finite place a uniformizer contributes the norm
of its prime ideal; at infinity we divide by the normalized archimedean
norm.  This is the convention for which principal ideles have norm one.
-/

open scoped NumberField RestrictedProduct NNReal
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

/-- The norm of a unit in a normed field, as a positive real unit. -/
def nnnormUnitHom (F : Type*) [NormedField F] :
    Fˣ →* ℝ≥0ˣ :=
  Units.map (nnnormHom : F →*₀ ℝ≥0).toMonoidHom

@[simp]
theorem nnnormUnitHom_val (F : Type*) [NormedField F] (x : Fˣ) :
    ((nnnormUnitHom F x : ℝ≥0ˣ) : ℝ≥0) = ‖(x : F)‖₊ :=
  rfl

namespace FiniteIdeleGroup

/-- The positive real unit given by the absolute norm of a finite prime. -/
def primeNorm (v : HeightOneSpectrum (𝓞 K)) : ℝ≥0ˣ :=
  Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (HeightOneSpectrum.absNorm_ne_zero v)

end FiniteIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The local integral-unit subgroup is open in the multiplicative group of a
finite completion. -/
theorem isOpen_finiteLocalUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen
      ((v.adicCompletionIntegers K).units :
        Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_GaloisCohomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Cyclic Tate low-degree boundary

For a finite cyclic group generated by `g`, mathlib computes odd group
cohomology using `Rep.FiniteCyclicGroup.subCompNormHom A g`.  The canonical
boundary comparison identifies that short-complex homology with
`tateCohomology A (-1)`.

This file applies that comparison to unit representations.  The resulting
objects are mathlib's Tate cohomology objects directly; no parallel
low-degree model is introduced.
-/

noncomputable section

open CategoryTheory

theorem zpowers_eq_top_of_forall_mem_zpowers {G : Type} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Subgroup.zpowers g = ⊤ := by
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact hg x

theorem isCyclic_of_forall_mem_zpowers {G : Type} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  exact ⟨g, zpowers_eq_top_of_forall_mem_zpowers g hg⟩

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of binary products

This specializes the dependent-product calculation to two possibly
different coefficient groups.  It is used to join the unrestricted and
integral parts of a supported idele group.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} [Group G] [Fintype G]
variable (A B : Type uA)
variable [CommGroup A] [CommGroup B]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]

/-- The two-element dependent family associated with `A × B`. -/
abbrev BinaryCoefficientFamily : Bool → Type uA
  | false => A
  | true => B

instance binaryCoefficientFamilyCommGroup :
    ∀ i, CommGroup (BinaryCoefficientFamily A B i)
  | false => inferInstance
  | true => inferInstance

/-- The componentwise `G`-action on the binary coefficient family. -/
@[reducible]
noncomputable def binaryCoefficientFamilyAction :
    ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i)
  | false => inferInstance
  | true => inferInstance

noncomputable instance
    (i : Bool) :
    MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
  binaryCoefficientFamilyAction A B i

/-- Reindex a binary product as a dependent family over `Bool`. -/
noncomputable def prodEquivBinaryCoefficientFamily :
    A × B ≃* ∀ i, BinaryCoefficientFamily A B i where
  toFun x
    | false => x.1
    | true => x.2
  invFun x := ⟨x false, x true⟩
  left_inv _ := rfl
  right_inv x := by
    funext i
    cases i <;> rfl
  map_mul' _ _ := by
    funext i
    cases i <;> rfl

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_NormalBasisLattice
attribute [-instance] _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public normal-basis lattice declarations used in Herbrand computations. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The `Gal(L / K)` orbit of Mathlib's normal-basis generator spans `L` over `K`. -/
theorem normalBasisConjugates_span_eq_top :
    Submodule.span K
        (Set.range (fun σ : Gal(L / K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L / K))))) = ⊤ := by
  have hset :
      Set.range (fun σ : Gal(L / K) =>
        σ (IsGalois.normalBasis K L (1 : Gal(L / K)))) =
        Set.range (IsGalois.normalBasis K L) := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, IsGalois.normalBasis_apply (K := K) (L := L) σ⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, (IsGalois.normalBasis_apply (K := K) (L := L) σ).symm⟩
  rw [hset]
  exact (IsGalois.normalBasis K L).span_eq

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The finite inverse-correction sum
`(-x) + (-x)^2 + ... + (-x)^d`.

When `x` is topologically nilpotent and the lattice is complete, these are the
finite approximations to `(1+x)⁻¹ - 1`. -/
def inverseCorrectionPartialSum (x : L) (d : Nat) : L :=
  (Finset.range d).sum fun i => (-x) ^ (i + 1)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- If every term of a convergent sequence lies in a closed submodule, then the
limit lies in that submodule. -/
theorem submodule_mem_of_tendsto_of_forall_mem_of_closed
    [TopologicalSpace L] {E : Submodule 𝒪[K] L} {f : Nat → L} {x : L}
    (hclosed : IsClosed (E : Set L)) (hf : Tendsto f atTop (nhds x))
    (hmem : ∀ d : Nat, f d ∈ E) :
    x ∈ E := by
  exact hclosed.mem_of_tendsto hf (Eventually.of_forall hmem)

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The inclusion `𝒪_L -> L` as an `𝒪_K`-linear map, using the valuation-extension
map `𝒪_K -> 𝒪_L` for the scalar action. -/
def integerRingToFieldLinearMap : 𝒪[L] →ₗ[𝒪[K]] L where
  toFun x := (x : L)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

end
end CyclicCohomology

universe u

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-! ### Additive quotient boundary -/

/-- The subgroup of `Vn` obtained from an included next-step subgroup
`Vsucc ≤ Vn`.  This is the denominator used for the multiplicative quotient
`V^n / V^(n+1)`. -/
def chosenNormalBasisPrincipalUnitSuccSubgroup {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (_hV : Vsucc ≤ Vn) : Subgroup Vn :=
  Vsucc.subgroupOf Vn

/-- Characterizes membership in the next normal-basis principal-unit subgroup. -/
theorem mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    u ∈ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc := by
  rw [chosenNormalBasisPrincipalUnitSuccSubgroup]
  exact Subgroup.mem_subgroupOf

/-- The multiplicative successive quotient `Vn / Vsucc`, for an actual inclusion
`Vsucc ≤ Vn`. -/
def chosenNormalBasisPrincipalUnitSuccQuot
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) : Type u :=
  Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV

/-- The quotient by the next normal-basis principal-unit subgroup is a commutative group. -/
instance chosenNormalBasisPrincipalUnitSuccQuotCommGroup
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    CommGroup (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  change CommGroup
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  infer_instance

/-- Explicit access to the concrete group quotient implementing the chosen
normal-basis principal-unit graded piece. -/
def chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) := by
  change
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) ≃*
      (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact MulEquiv.refl _

/-- The quotient map `Vn -> Vn / Vsucc`. -/
def chosenNormalBasisPrincipalUnitSuccQuotMk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    Vn →* chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV := by
  change Vn →*
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact QuotientGroup.mk'
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Lattice
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Permutation-stable sublattices

This file proves the permutation-stable sublattice lemma.  The proof
also handles a
permutation basis with more than one orbit: approximate every large coordinate
vector by a lattice point and average all these approximations equivariantly
over the finite group.
-/

noncomputable section

namespace CyclicCohomology

open Module Submodule
open scoped BigOperators

universe uG uι

variable {G : Type uG} {ι : Type uι}

/-- The linear coordinate permutation attached to a permutation of the
indexing type. -/
def coordinatePermutation (σ : Equiv.Perm ι) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coordinatePermutation_apply
    (σ : Equiv.Perm ι) (x : ι → ℝ) (i : ι) :
    coordinatePermutation σ x i = x (σ.symm i) :=
  rfl

@[simp]
theorem coordinatePermutation_refl :
    coordinatePermutation (Equiv.refl ι) =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  ext x i
  rfl

theorem coordinatePermutation_mul
    (σ τ : Equiv.Perm ι) :
    coordinatePermutation (σ * τ) =
      (coordinatePermutation τ).trans
        (coordinatePermutation σ) := by
  ext x i
  rfl

@[simp]
theorem coordinatePermutation_inv
    (σ : Equiv.Perm ι) :
    coordinatePermutation σ⁻¹ =
      (coordinatePermutation σ).symm := by
  rw [show σ⁻¹ = σ.symm from rfl]
  ext x i
  rfl

@[simp]
theorem coordinatePermutation_single
    [DecidableEq ι] (σ : Equiv.Perm ι) (i : ι) :
    coordinatePermutation σ (Pi.single i (1 : ℝ)) =
      Pi.single (σ i) 1 := by
  ext j
  by_cases h : j = σ i
  · subst j
    simp
  · have h' : σ.symm j ≠ i := by
      intro hij
      apply h
      simpa using congrArg σ hij
    simp [coordinatePermutation_apply, h, h']

section Approximation

variable [Fintype ι]

/-- A canonical lattice point whose difference from `x` lies in the
fundamental parallelepiped of a chosen lattice basis. -/
def latticeApproximation
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) : L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  refine ⟨ZSpan.floor bℝ x, ?_⟩
  let z : ι → ℝ := (ZSpan.floor bℝ x).1
  change z ∈ L
  rw [← b.ofZLatticeBasis_span ℝ]
  exact (ZSpan.floor bℝ x).property

/-- A uniform approximation radius for the canonical lattice
approximation. -/
def latticeApproximationRadius
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  ∑ i, ‖bℝ i‖

theorem latticeApproximationRadius_nonneg
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    0 ≤ latticeApproximationRadius L := by
  unfold latticeApproximationRadius
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem norm_sub_latticeApproximation_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) :
    ‖x - (latticeApproximation L x : ι → ℝ)‖ ≤
      latticeApproximationRadius L := by
  let b : Basis ι ℤ L := IsZLattice.basis L
  let bℝ : Basis ι ℝ (ι → ℝ) := b.ofZLatticeBasis ℝ L
  simpa only [latticeApproximation, latticeApproximationRadius,
    ZSpan.fract] using ZSpan.norm_fract_le bℝ x

theorem abs_latticeApproximation_sub_apply_le
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : ι → ℝ) (i : ι) :
    |(latticeApproximation L x : ι → ℝ) i - x i| ≤
      latticeApproximationRadius L := by
  have hcoord :
      ‖(x - (latticeApproximation L x : ι → ℝ)) i‖ ≤
        ‖x - (latticeApproximation L x : ι → ℝ)‖ :=
    norm_le_pi_norm (x - (latticeApproximation L x : ι → ℝ)) i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] at hcoord
  exact hcoord.trans (norm_sub_latticeApproximation_le L x)

end Approximation

section Averaging

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The action of `g` on the coordinate space for a permutation
representation `ρ`. -/
def permutationRepresentation
    (ρ : G →* Equiv.Perm ι) (g : G) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  coordinatePermutation (ρ g)

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
@[simp]
theorem permutationRepresentation_one
    (ρ : G →* Equiv.Perm ι) :
    permutationRepresentation ρ 1 =
      LinearEquiv.refl ℝ (ι → ℝ) := by
  change coordinatePermutation (ρ 1) =
    LinearEquiv.refl ℝ (ι → ℝ)
  rw [map_one]
  exact coordinatePermutation_refl

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
theorem permutationRepresentation_mul
    (ρ : G →* Equiv.Perm ι) (g h : G) :
    permutationRepresentation ρ (g * h) =
      (permutationRepresentation ρ h).trans
        (permutationRepresentation ρ g) := by
  simp only [permutationRepresentation, map_mul]
  exact coordinatePermutation_mul _ _

/-- Restrict a permutation representation to an invariant lattice. -/
def permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) : L ≃ₗ[ℤ] L where
  toFun x :=
    ⟨permutationRepresentation ρ g x.1, hL g x.1 x.2⟩
  invFun x :=
    ⟨permutationRepresentation ρ g⁻¹ x.1,
      hL g⁻¹ x.1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g⁻¹)
      (coordinatePermutation (ρ g) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    change coordinatePermutation (ρ g)
      (coordinatePermutation (ρ g⁻¹) x.1) = x.1
    rw [map_inv,
      coordinatePermutation_inv]
    exact (coordinatePermutation (ρ g)).apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' n x := by
    apply Subtype.ext
    exact map_zsmul _ _ _

omit [Fintype G] [Fintype ι] [DecidableEq ι] in
@[simp]
theorem coe_permutationLatticeEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ))
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (x : L) :
    ((permutationLatticeEquiv ρ L hL g x : L) : ι → ℝ) =
      permutationRepresentation ρ g x :=
  rfl

/-- The equivariant average of lattice approximations to the large
coordinate vectors. -/
def averagedLatticeVector
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) : L :=
  ∑ g : G,
    permutationLatticeEquiv ρ L hL g
      (latticeApproximation L
        (t • Pi.single ((ρ g).symm i) (1 : ℝ)))

/-- A scale large enough to make the averaged lattice vectors strictly
column diagonally dominant. -/
def permutationLatticeScale
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ℝ :=
  ((Fintype.card ι : ℝ) + 1) *
      latticeApproximationRadius L + 1

@[simp]
theorem averagedLatticeVector_apply
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i j : ι) :
    (averagedLatticeVector ρ L hL t i : ι → ℝ) j =
      ∑ g : G,
        (latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
            ι → ℝ) ((ρ g).symm j) := by
  simp [averagedLatticeVector, permutationRepresentation]

omit [Fintype G] in
theorem averagingSummand_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) (i : ι) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i) - t| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm i)
  simpa using h

omit [Fintype G] in
theorem averagingSummand_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L] (t : ℝ) (g : G) {i j : ι}
    (hji : j ≠ i) :
    |(latticeApproximation L
          (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)| ≤
      latticeApproximationRadius L := by
  have h :=
    abs_latticeApproximation_sub_apply_le L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ))
      ((ρ g).symm j)
  have hne : (ρ g).symm j ≠ (ρ g).symm i :=
    (ρ g).symm.injective.ne hji
  simpa [hne] using h

theorem averagedLatticeVector_diagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (i : ι) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) i -
        (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm i)
  change |(∑ g : G, a g) -
    (Fintype.card G : ℝ) * t| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L
  have ha (g : G) :
      |a g - t| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_diagonal_bound ρ L t g i
  have heq :
      (∑ g : G, a g) -
          (Fintype.card G : ℝ) * t =
        ∑ g : G, (a g - t) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    |∑ g : G, (a g - t)| ≤
        ∑ g : G, |a g - t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

theorem averagedLatticeVector_offDiagonal_bound
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) {i j : ι} (hji : j ≠ i) :
    |(averagedLatticeVector ρ L hL t i : ι → ℝ) j| ≤
      (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by
  rw [averagedLatticeVector_apply]
  let a : G → ℝ := fun g ↦
    (latticeApproximation L
      (t • Pi.single ((ρ g).symm i) (1 : ℝ)) :
        ι → ℝ) ((ρ g).symm j)
  change |∑ g : G, a g| ≤
    (Fintype.card G : ℝ) *
      latticeApproximationRadius L
  have ha (g : G) :
      |a g| ≤ latticeApproximationRadius L := by
    simpa only [a] using
      averagingSummand_offDiagonal_bound
        ρ L t g hji
  calc
    |∑ g : G, a g| ≤ ∑ g : G, |a g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : G, latticeApproximationRadius L :=
      Finset.sum_le_sum fun g _ ↦ ha g
    _ = (Fintype.card G : ℝ) *
        latticeApproximationRadius L := by simp

/-- The coordinate matrix whose columns are the averaged lattice
vectors. -/
def averagedLatticeMatrix
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) : Matrix ι ι ℝ :=
  fun row column ↦
    (averagedLatticeVector ρ L hL t column :
      ι → ℝ) row

theorem averagedLatticeMatrix_sum_col_lt_diag
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∀ k : ι,
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) j k‖ <
        ‖averagedLatticeMatrix ρ L hL
            (permutationLatticeScale L) k k‖ := by
  intro k
  let B : ℝ := latticeApproximationRadius L
  let n : ℝ := Fintype.card G
  let s : ℝ := Fintype.card ι
  let t : ℝ := permutationLatticeScale L
  let E : ℝ := n * B
  have hB : 0 ≤ B :=
    latticeApproximationRadius_nonneg L
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hs : 0 ≤ s := by positivity
  have hE : 0 ≤ E := mul_nonneg hn.le hB
  have hoff (j : ι) (hjk : j ≠ k) :
      ‖averagedLatticeMatrix ρ L hL t j k‖ ≤ E := by
    change
      |(averagedLatticeVector ρ L hL t k :
        ι → ℝ) j| ≤ E
    exact averagedLatticeVector_offDiagonal_bound
      ρ L hL t hjk
  have hsum :
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
        s * E := by
    calc
      ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ ≤
          ∑ _j ∈ Finset.univ.erase k, E :=
        Finset.sum_le_sum fun j hj ↦
          hoff j (Finset.ne_of_mem_erase hj)
      _ ≤ ∑ _j : ι, E :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset k Finset.univ)
          (fun _ _ _ ↦ hE)
      _ = s * E := by simp [s]
  have hdiag :
      |(averagedLatticeMatrix ρ L hL t k k) -
          n * t| ≤ E := by
    exact averagedLatticeVector_diagonal_bound
      ρ L hL t k
  have hdiagLower :
      n * t - E ≤
        |averagedLatticeMatrix ρ L hL t k k| := by
    have hleft := (abs_le.mp hdiag).1
    have hself :
        averagedLatticeMatrix ρ L hL t k k ≤
          |averagedLatticeMatrix ρ L hL t k k| :=
      le_abs_self _
    nlinarith
  have hnumeric : s * E < n * t - E := by
    dsimp only [E, n, s, t, B]
    unfold permutationLatticeScale
    nlinarith
  calc
    ∑ j ∈ Finset.univ.erase k,
        ‖averagedLatticeMatrix ρ L hL
          (permutationLatticeScale L) j k‖ =
        ∑ j ∈ Finset.univ.erase k,
          ‖averagedLatticeMatrix ρ L hL t j k‖ := by rfl
    _ ≤ s * E := hsum
    _ < n * t - E := hnumeric
    _ ≤ |averagedLatticeMatrix ρ L hL t k k| :=
      hdiagLower
    _ = ‖averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) k k‖ := by
      rfl

theorem averagedLatticeMatrix_det_ne_zero
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    (averagedLatticeMatrix ρ L hL
      (permutationLatticeScale L)).det ≠ 0 :=
  det_ne_zero_of_sum_col_lt_diag
    (averagedLatticeMatrix_sum_col_lt_diag ρ L hL)

theorem averagedLatticeVector_linearIndependent
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    LinearIndependent ℝ
      (fun i ↦
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i :
            ι → ℝ)) := by
  have hcols :=
    Matrix.linearIndependent_cols_of_det_ne_zero
      (averagedLatticeMatrix_det_ne_zero ρ L hL)
  change LinearIndependent ℝ
    (fun i j ↦
      averagedLatticeMatrix ρ L hL
        (permutationLatticeScale L) j i) at hcols
  simpa only [averagedLatticeMatrix] using hcols

theorem averagedLatticeVector_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (t : ℝ) (g : G) (i : ι) :
    permutationLatticeEquiv ρ L hL g
        (averagedLatticeVector ρ L hL t i) =
      averagedLatticeVector ρ L hL t (ρ g i) := by
  classical
  apply Subtype.ext
  ext j
  simp only [coe_permutationLatticeEquiv,
    permutationRepresentation, coordinatePermutation_apply,
    averagedLatticeVector_apply]
  let F : G → ℝ := fun h ↦
      (latticeApproximation L
        (t • Pi.single ((ρ h).symm i) (1 : ℝ)) :
          ι → ℝ) ((ρ h).symm ((ρ g).symm j))
  let H : G → ℝ := fun k ↦
      (latticeApproximation L
        (t • Pi.single ((ρ k).symm (ρ g i)) (1 : ℝ)) :
          ι → ℝ) ((ρ k).symm j)
  have hterm (h : G) : F h = H (g * h) := by
    dsimp only [F, H]
    have hindex :
        (ρ (g * h)).symm (ρ g i) = (ρ h).symm i := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    have hcoordinate :
        (ρ (g * h)).symm j =
          (ρ h).symm ((ρ g).symm j) := by
      rw [Equiv.symm_apply_eq]
      simp [map_mul]
    rw [hindex, hcoordinate]
  calc
    ∑ h : G, F h = ∑ h : G, H (g * h) := by
      exact Finset.sum_congr rfl fun h _ ↦ hterm h
    _ = ∑ k : G, H k := by
      exact Fintype.sum_bijective (g * ·)
        (Group.mulLeft_bijective g) (fun h ↦ H (g * h)) H
        fun _ ↦ rfl

/-- The complete sublattice generated by the equivariantly averaged
vectors. -/
def permutationSublattice
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ
    (Set.range fun i ↦
      (averagedLatticeVector ρ L hL
        (permutationLatticeScale L) i : ι → ℝ))

theorem permutationSublattice_le
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    permutationSublattice ρ L hL ≤ L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (averagedLatticeVector ρ L hL
    (permutationLatticeScale L) i).property

instance permutationSublattice_discreteTopology
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DiscreteTopology (permutationSublattice ρ L hL) := by
  let f : permutationSublattice ρ L hL → L :=
    fun x ↦ ⟨x.1, permutationSublattice_le ρ L hL x.2⟩
  refine DiscreteTopology.of_continuous_injective
    (f := f) ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val _
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : L ↦ (z : ι → ℝ)) hxy

theorem permutationSublattice_span_eq_top
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Submodule.span ℝ
        (permutationSublattice ρ L hL :
          Set (ι → ℝ)) = ⊤ := by
  let w : ι → (ι → ℝ) := fun i ↦
    (averagedLatticeVector ρ L hL
      (permutationLatticeScale L) i : ι → ℝ)
  have hw :
      LinearIndependent ℝ w :=
    averagedLatticeVector_linearIndependent ρ L hL
  have hwspan :
      Submodule.span ℝ (Set.range w) = ⊤ :=
    hw.span_eq_top_of_card_eq_finrank'
      (Module.finrank_fintype_fun_eq_card ℝ).symm
  rw [eq_top_iff, ← hwspan]
  apply Submodule.span_mono (R := ℝ)
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, rfl⟩

instance permutationSublattice_isZLattice
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    IsZLattice ℝ (permutationSublattice ρ L hL) where
  span_top := permutationSublattice_span_eq_top ρ L hL

/-- The distinguished basis of the permutation-stable sublattice. -/
def permutationSublatticeBasis
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Basis ι ℤ (permutationSublattice ρ L hL) :=
  Basis.span
    ((averagedLatticeVector_linearIndependent ρ L hL).restrict_scalars' ℤ)

@[simp]
theorem permutationSublatticeBasis_apply_coe
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (i : ι) :
    ((permutationSublatticeBasis ρ L hL i :
        permutationSublattice ρ L hL) : ι → ℝ) =
      averagedLatticeVector ρ L hL
        (permutationLatticeScale L) i := by
  let hli :=
    (averagedLatticeVector_linearIndependent
      ρ L hL).restrict_scalars' ℤ
  change
    ((Basis.span hli i :
      permutationSublattice ρ L hL) : ι → ℝ) =
        (averagedLatticeVector ρ L hL
          (permutationLatticeScale L) i : ι → ℝ)
  exact Basis.coe_span_apply hli i

theorem permutationSublatticeBasis_permuted
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (i : ι) :
    permutationRepresentation ρ g
        (permutationSublatticeBasis ρ L hL i :
          ι → ℝ) =
      (permutationSublatticeBasis ρ L hL (ρ g i) :
        ι → ℝ) := by
  have h :=
    congrArg (fun x : L ↦ (x : ι → ℝ))
      (averagedLatticeVector_equivariant
        ρ L hL (permutationLatticeScale L) g i)
  simpa only [coe_permutationLatticeEquiv,
    permutationSublatticeBasis_apply_coe] using h

end Averaging

section FiniteIndex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Two complete integral lattices in the same real vector space are
commensurable: if one is contained in the other, its quotient in the
larger lattice is finite. -/
theorem finite_quotient_of_complete_sublattice
    (L L' : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology L'] [IsZLattice ℝ L']
    (hL' : L' ≤ L) :
    Finite (L ⧸ L'.comap L.subtype) := by
  let N : Submodule ℤ L := L'.comap L.subtype
  let e : N ≃ₗ[ℤ] L' :=
    Submodule.comapSubtypeEquivOfLe hL'
  let : Module.Finite ℤ L :=
    ZLattice.module_finite ℝ L
  have hrank : Module.finrank ℤ N =
      Module.finrank ℤ L := by
    calc
      Module.finrank ℤ N =
          Module.finrank ℤ L' :=
        LinearEquiv.finrank_eq e
      _ = Module.finrank ℝ E :=
        ZLattice.rank ℝ L'
      _ = Module.finrank ℤ L :=
        (ZLattice.rank ℝ L).symm
  exact
    Submodule.finiteQuotientOfFreeOfRankEq
      (L'.comap L.subtype) hrank

end FiniteIndex

section PermutationFiniteIndex

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The canonical permutation sublattice has
finite index in the original complete invariant lattice. -/
theorem permutationSublattice_finite_quotient
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (L ⧸
        (permutationSublattice ρ L hL).comap
          L.subtype) :=
  finite_quotient_of_complete_sublattice
    L (permutationSublattice ρ L hL)
      (permutationSublattice_le ρ L hL)

end PermutationFiniteIndex

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_LatticeHerbrand
attribute [-instance] _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of complete permutation sublattices

This file connects the complete permutation sublattice with its
orbit-stabilizer Herbrand quotient calculation.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open Module Submodule
open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι

variable {G : Type uG} {ι : Type uι}

/-- The action on an indexing type specified by a permutation
representation. -/
@[reducible]
def permutationMulAction
    [Group G] (ρ : G →* Equiv.Perm ι) :
    MulAction G ι where
  smul g i := ρ g i
  one_smul i := by
    change ρ 1 i = i
    rw [map_one]
    rfl
  mul_smul g h i := by
    change ρ (g * h) i = ρ g (ρ h i)
    rw [map_mul]
    rfl

/-- Coordinate permutation over the integers. -/
def intCoordinatePermutation (σ : Equiv.Perm ι) :
    (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section IntegralPermutationBasis

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module ℤ M]

omit [Fintype G] in
/-- Coordinates in a basis permuted by `G` transform by the
contragredient coordinate permutation. -/
theorem basisEquivFun_symm_intCoordinatePermutation
    (b : Basis ι ℤ M)
    (ρ : G →* Equiv.Perm ι)
    (α : G →* (M ≃ₗ[ℤ] M))
    (hb : ∀ (g : G) (i : ι),
      α g (b i) = b (ρ g i))
    (g : G) (x : ι → ℤ) :
    b.equivFun.symm
        (intCoordinatePermutation (ρ g) x) =
      α g (b.equivFun.symm x) := by
  have hmaps :
      b.equivFun.symm.toLinearMap.comp
          (intCoordinatePermutation (ρ g)).toLinearMap =
        (α g).toLinearMap.comp
          b.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun ℤ ι).ext
    intro i
    simp only [LinearMap.comp_apply, Pi.basisFun_apply]
    have hsingle (j : ι) :
        b.equivFun.symm (Pi.single j 1) = b j := by
      exact _root_.Basis.equivFun_symm_single b j
    calc
      b.equivFun.symm
          (intCoordinatePermutation (ρ g)
            (Pi.single i 1)) =
          b.equivFun.symm
            (Pi.single (ρ g i) 1) := by
              congr 1
              ext j
              by_cases h : j = ρ g i
              · subst j
                simp [intCoordinatePermutation]
              · have h' : (ρ g).symm j ≠ i := by
                  intro hij
                  apply h
                  simpa using congrArg (ρ g) hij
                simp [intCoordinatePermutation, h, h']
      _ = b (ρ g i) := hsingle (ρ g i)
      _ = α g (b i) := (hb g i).symm
      _ = α g
          (b.equivFun.symm (Pi.single i 1)) := by
        rw [hsingle i]
  exact LinearMap.congr_fun hmaps x

end IntegralPermutationBasis

section StableSublattice

variable [Fintype G] [Group G] [Fintype ι] [DecidableEq ι]

/-- The canonical permutation sublattice is stable under the
permutation representation. -/
theorem permutationSublattice_stable
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    ∀ (g : G) (x : ι → ℝ),
      x ∈ permutationSublattice ρ L hL →
        permutationRepresentation ρ g x ∈
          permutationSublattice ρ L hL := by
  intro g x hx
  rw [permutationSublattice] at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    have heq :
        permutationRepresentation ρ g
            (averagedLatticeVector ρ L hL
              (permutationLatticeScale L) i : ι → ℝ) =
          (averagedLatticeVector ρ L hL
            (permutationLatticeScale L) (ρ g i) :
              ι → ℝ) := by
      have h :=
        congrArg (fun q : L => (q : ι → ℝ))
          (averagedLatticeVector_equivariant
            ρ L hL (permutationLatticeScale L) g i)
      simpa only [coe_permutationLatticeEquiv] using h
    rw [heq]
    exact Submodule.subset_span ⟨ρ g i, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro n y _ hy
    rw [map_zsmul]
    exact Submodule.smul_mem _ n hy

/-- The additive action on the canonical permutation sublattice. -/
@[reducible]
def permutationSublatticeDistribMulAction
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DistribMulAction G (permutationSublattice ρ L hL) where
  smul g x :=
    ⟨permutationRepresentation ρ g x.1,
      permutationSublattice_stable ρ L hL g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change permutationRepresentation ρ 1 x.1 = x.1
    rw [permutationRepresentation_one]
    rfl
  mul_smul g h x := by
    apply Subtype.ext
    change
      permutationRepresentation ρ (g * h) x.1 =
        permutationRepresentation ρ g
          (permutationRepresentation ρ h x.1)
    rw [permutationRepresentation_mul]
    rfl
  smul_zero g := by
    apply Subtype.ext
    exact map_zero (permutationRepresentation ρ g)
  smul_add g x y := by
    apply Subtype.ext
    exact map_add (permutationRepresentation ρ g) x.1 y.1

/-- An additive action, written multiplicatively. -/
@[reducible]
def multiplicativeDistribMulAction
    {A : Type*} [AddCommGroup A]
    [DistribMulAction G A] :
    MulDistribMulAction G (Multiplicative A) where
  smul g x := Multiplicative.ofAdd (g • Multiplicative.toAdd x)
  one_smul x := congrArg Multiplicative.ofAdd
    (one_smul G (Multiplicative.toAdd x))
  mul_smul g h x := congrArg Multiplicative.ofAdd
    (mul_smul g h (Multiplicative.toAdd x))
  smul_one g := congrArg Multiplicative.ofAdd
    (DistribMulAction.smul_zero g)
  smul_mul g x y := congrArg Multiplicative.ofAdd
    (DistribMulAction.smul_add g
      (Multiplicative.toAdd x) (Multiplicative.toAdd y))

/-- A submodule, written as a subgroup of the multiplicative copy of
its ambient additive group. -/
@[reducible]
def multiplicativeSubmoduleSubgroup
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) :
    Subgroup (Multiplicative M) :=
  N.toAddSubgroup.toSubgroup

/-- The multiplicative copy of a submodule is canonically equivalent
to the corresponding subgroup of the multiplicative ambient group. -/
def multiplicativeSubmoduleMulEquiv
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M) :
    Multiplicative N ≃*
      multiplicativeSubmoduleSubgroup N where
  toFun x :=
    ⟨Multiplicative.ofAdd
        ((Multiplicative.toAdd x : N) : M),
      (Multiplicative.toAdd x : N).property⟩
  invFun x :=
    Multiplicative.ofAdd
      ⟨Multiplicative.toAdd x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Finiteness of an additive submodule quotient is unchanged after
passing to multiplicative notation. -/
theorem multiplicativeSubmoduleQuotientFinite
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (N : Submodule ℤ M)
    [Finite (M ⧸ N)] :
    Finite
      (Multiplicative M ⧸
        multiplicativeSubmoduleSubgroup N) := by
  let f :
      Multiplicative M →*
        Multiplicative (M ⧸ N) :=
    (QuotientAddGroup.mk'
      N.toAddSubgroup).toMultiplicative
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ :=
      QuotientAddGroup.mk'_surjective
        N.toAddSubgroup
        (Multiplicative.toAdd y)
    exact
      ⟨Multiplicative.ofAdd x,
        congrArg Multiplicative.ofAdd hx⟩
  have hker :
      f.ker =
        multiplicativeSubmoduleSubgroup N := by
    change
      (QuotientAddGroup.mk'
          N.toAddSubgroup).ker.toSubgroup =
        N.toAddSubgroup.toSubgroup
    rw [QuotientAddGroup.ker_mk']
  let e :
      Multiplicative M ⧸
          multiplicativeSubmoduleSubgroup N ≃*
        Multiplicative (M ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact
    Finite.of_equiv
      (Multiplicative (M ⧸ N)) e.symm.toEquiv

/-- The action on any complete stable lattice induced by its
permutation representation. -/
@[reducible]
def completePermutationLatticeDistribMulAction
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    DistribMulAction G L where
  smul g x :=
    ⟨permutationRepresentation ρ g x.1,
      hL g x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change permutationRepresentation ρ 1 x.1 = x.1
    rw [permutationRepresentation_one]
    rfl
  mul_smul g h x := by
    apply Subtype.ext
    change
      permutationRepresentation ρ (g * h) x.1 =
        permutationRepresentation ρ g
          (permutationRepresentation ρ h x.1)
    rw [permutationRepresentation_mul]
    rfl
  smul_zero g := by
    apply Subtype.ext
    exact map_zero (permutationRepresentation ρ g)
  smul_add g x y := by
    apply Subtype.ext
    exact map_add (permutationRepresentation ρ g) x.1 y.1

/-- The canonical complete permutation sublattice, viewed as a
subgroup of the multiplicative copy of the ambient lattice. -/
noncomputable def permutationSublatticeMultiplicativeSubgroup
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Subgroup (Multiplicative L) :=
  multiplicativeSubmoduleSubgroup
    ((permutationSublattice ρ L hL).comap L.subtype)

/-- The permutation-sublattice subgroup is stable under the ambient
lattice action. -/
theorem
    permutationSublatticeMultiplicativeSubgroup_stable
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    ∀ (g : G) (x : Multiplicative L),
      x ∈
          permutationSublatticeMultiplicativeSubgroup
            ρ L hL →
        g • x ∈
          permutationSublatticeMultiplicativeSubgroup
            ρ L hL := by
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  intro g x hx
  change
    permutationRepresentation ρ g
        ((Multiplicative.toAdd x : L) : ι → ℝ) ∈
      permutationSublattice ρ L hL
  change
    ((Multiplicative.toAdd x : L) : ι → ℝ) ∈
      permutationSublattice ρ L hL at hx
  exact
    permutationSublattice_stable
      ρ L hL g _ hx

/-- The canonical permutation-sublattice subgroup has finite quotient
in the multiplicative ambient lattice. -/
theorem
    permutationSublatticeMultiplicativeSubgroup_finite_quotient
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Finite
      (Multiplicative L ⧸
        permutationSublatticeMultiplicativeSubgroup
          ρ L hL) := by
  let N :
      Submodule ℤ L :=
    (permutationSublattice ρ L hL).comap
      L.subtype
  let quotientFinite : Finite (L ⧸ N) :=
    permutationSublattice_finite_quotient
      ρ L hL
  exact
    multiplicativeSubmoduleQuotientFinite N

/-- The subgroup cut out by the canonical permutation sublattice is
canonically the multiplicative copy of that sublattice. -/
noncomputable def
    permutationSublatticeSubgroupMulEquiv
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    permutationSublatticeMultiplicativeSubgroup
        ρ L hL ≃*
      Multiplicative
        (permutationSublattice ρ L hL) :=
  (multiplicativeSubmoduleMulEquiv
      ((permutationSublattice ρ L hL).comap
        L.subtype)).symm.trans
    (Submodule.comapSubtypeEquivOfLe
        (permutationSublattice_le ρ L hL)).toAddEquiv.toMultiplicative

/-- The canonical identification of the finite-index subgroup with
the permutation sublattice is equivariant. -/
theorem
    permutationSublatticeSubgroupMulEquiv_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _ambientAction :
        DistribMulAction G L :=
      completePermutationLatticeDistribMulAction
        ρ L hL
    letI _ambientMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative L) :=
      multiplicativeDistribMulAction
    letI _subgroupAction :
        MulDistribMulAction G
          (permutationSublatticeMultiplicativeSubgroup
            ρ L hL) :=
      stableSubgroupMulDistribMulAction
        (permutationSublatticeMultiplicativeSubgroup
          ρ L hL)
        (permutationSublatticeMultiplicativeSubgroup_stable
          ρ L hL)
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _sublatticeMultiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    ∀ (g : G)
      (x :
        permutationSublatticeMultiplicativeSubgroup
          ρ L hL),
      permutationSublatticeSubgroupMulEquiv
          ρ L hL (g • x) =
        g •
          permutationSublatticeSubgroupMulEquiv
            ρ L hL x := by
  let ambientAction :
      DistribMulAction G L :=
    completePermutationLatticeDistribMulAction
      ρ L hL
  let ambientMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative L) :=
    multiplicativeDistribMulAction
  let subgroupAction :
      MulDistribMulAction G
        (permutationSublatticeMultiplicativeSubgroup
          ρ L hL) :=
    stableSubgroupMulDistribMulAction
      (permutationSublatticeMultiplicativeSubgroup
        ρ L hL)
      (permutationSublatticeMultiplicativeSubgroup_stable
        ρ L hL)
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let sublatticeMultiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  intro g x
  rfl

/-- The integral-linear automorphisms underlying the action on the
canonical permutation sublattice. -/
noncomputable def permutationSublatticeModuleAut
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    G →* (permutationSublattice ρ L hL ≃ₗ[ℤ]
      permutationSublattice ρ L hL) := by
  letI :=
    permutationSublatticeDistribMulAction ρ L hL
  exact DistribMulAction.toModuleAut ℤ
    (permutationSublattice ρ L hL)

/-- Multiplicative coordinates in the distinguished integral basis of
the canonical permutation sublattice. -/
noncomputable def permutationSublatticeBasisMulEquivFunctions
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    Multiplicative (permutationSublattice ρ L hL) ≃*
      (ι → Multiplicative ℤ) :=
  (AddEquiv.toMultiplicative
      (permutationSublatticeBasis ρ L hL).equivFun.toAddEquiv).trans
    (MulEquiv.funMultiplicative ι ℤ)

@[simp]
theorem permutationSublatticeModuleAut_basis
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L)
    (g : G) (i : ι) :
    permutationSublatticeModuleAut ρ L hL g
        (permutationSublatticeBasis ρ L hL i) =
      permutationSublatticeBasis ρ L hL (ρ g i) := by
  apply Subtype.ext
  exact permutationSublatticeBasis_permuted
    ρ L hL g i

/-- The distinguished basis coordinates identify the canonical
permutation sublattice equivariantly with integer-valued functions. -/
theorem permutationSublatticeBasisMulEquivFunctions_equivariant
    (ρ : G →* Equiv.Perm ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    [IsZLattice ℝ L]
    (hL : ∀ (g : G) (x : ι → ℝ), x ∈ L →
      permutationRepresentation ρ g x ∈ L) :
    letI _indexAction : MulAction G ι :=
      permutationMulAction ρ
    letI _sublatticeAction :
        DistribMulAction G
          (permutationSublattice ρ L hL) :=
      permutationSublatticeDistribMulAction ρ L hL
    letI _multiplicativeAction :
        MulDistribMulAction G
          (Multiplicative
            (permutationSublattice ρ L hL)) :=
      multiplicativeDistribMulAction
    letI _functionAction :
        MulDistribMulAction G
          (ι → Multiplicative ℤ) :=
      permutationFunctionMulDistribMulAction
    ∀ (g : G)
      (x : Multiplicative
        (permutationSublattice ρ L hL)),
      permutationSublatticeBasisMulEquivFunctions
          ρ L hL (g • x) =
        g • permutationSublatticeBasisMulEquivFunctions
          ρ L hL x := by
  let indexAction : MulAction G ι :=
    permutationMulAction ρ
  let sublatticeAction :
      DistribMulAction G
        (permutationSublattice ρ L hL) :=
    permutationSublatticeDistribMulAction ρ L hL
  let multiplicativeAction :
      MulDistribMulAction G
        (Multiplicative
          (permutationSublattice ρ L hL)) :=
    multiplicativeDistribMulAction
  let functionAction :
      MulDistribMulAction G
        (ι → Multiplicative ℤ) :=
    permutationFunctionMulDistribMulAction
  intro g x
  let b :=
    permutationSublatticeBasis ρ L hL
  ext i
  change
    b.equivFun (g • Multiplicative.toAdd x) i =
      b.equivFun (Multiplicative.toAdd x) (ρ g⁻¹ i)
  let α :=
    permutationSublatticeModuleAut ρ L hL
  have hinter :=
    basisEquivFun_symm_intCoordinatePermutation
      b ρ α
      (permutationSublatticeModuleAut_basis ρ L hL)
      g (b.equivFun (Multiplicative.toAdd x))
  have hcoord :=
    congrArg (fun y => b.equivFun y i) hinter
  have hα
      (y : permutationSublattice ρ L hL) :
      α g y = g • y :=
    rfl
  have hinv :
      ((ρ g)⁻¹ : Equiv.Perm ι) = (ρ g).symm :=
    rfl
  rw [map_inv, hinv]
  have hcoord' :
      (intCoordinatePermutation (ρ g)
        (b.equivFun (Multiplicative.toAdd x))) i =
        b.equivFun (g • Multiplicative.toAdd x) i := by
    simpa only [LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply, hα] using hcoord
  change
    b.equivFun (Multiplicative.toAdd x) ((ρ g).symm i) =
      b.equivFun (g • Multiplicative.toAdd x) i at hcoord'
  exact hcoord'.symm

end StableSublattice

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_Invariants
attribute [-instance] _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Invariant units

The actual invariant submodule of the unit representation, together with its
arithmetic identification with the units of the base field.
-/

namespace CyclicCohomology

noncomputable section

/-- The actual invariant submodule of the unit representation `Lˣ` under `Gal(L/K)`. -/
def unitsInvariantSubmodule (K L : Type) [Field K] [Field L] [Algebra K L] :
    Submodule ℤ (Additive Lˣ) :=
  (Rep.ofAlgebraAutOnUnits K L).ρ.invariants

noncomputable def invariantUnitToBaseUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) : Kˣ := by
  classical
  let y : Lˣ := Additive.toMul (x : Additive Lˣ)
  have hfixed : ∀ σ : Gal(L/K), σ (y : L) = (y : L) := by
    intro σ
    have h :=
      congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) (x.property σ)
    have hρ :
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (x : Additive Lˣ) =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul (x : Additive Lˣ))) :=
      rfl
    rw [hρ] at h
    simpa [y] using h
  have hmem : (y : L) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (y : L)).2 hfixed
  let a : K := Classical.choose hmem
  have ha : algebraMap K L a = (y : L) := Classical.choose_spec hmem
  have ha0 : a ≠ 0 := by
    intro hzero
    exact y.ne_zero (by rw [← ha, hzero, map_zero])
  exact ⟨a, a⁻¹, by simp [ha0], by simp [ha0]⟩

lemma invariantUnitToBaseUnit_spec (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    algebraMap K L (invariantUnitToBaseUnit K L x : K) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) := by
  classical
  let y : Lˣ := Additive.toMul (x : Additive Lˣ)
  have hfixed : ∀ σ : Gal(L/K), σ (y : L) = (y : L) := by
    intro σ
    have h :=
      congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) (x.property σ)
    have hρ :
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (x : Additive Lˣ) =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul (x : Additive Lˣ))) :=
      rfl
    rw [hρ] at h
    simpa [y] using h
  have hmem : (y : L) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (y : L)).2 hfixed
  change algebraMap K L (Classical.choose hmem) = (y : L)
  exact Classical.choose_spec hmem

noncomputable def baseUnitToInvariantUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] (x : Kˣ) : unitsInvariantSubmodule K L where
  val := Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)
  property := by
    intro σ
    change
      Additive.ofMul
          (Units.mapEquiv σ.toMulEquiv (Units.map (algebraMap K L).toMonoidHom x)) =
        Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)
    apply Additive.ofMul.injective
    ext
    simp

lemma invariantUnitToBaseUnit_baseUnitToInvariantUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : Kˣ) :
    invariantUnitToBaseUnit K L (baseUnitToInvariantUnit K L x) = x := by
  ext
  apply FaithfulSMul.algebraMap_injective K L
  rw [invariantUnitToBaseUnit_spec]
  rfl

lemma baseUnitToInvariantUnit_invariantUnitToBaseUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    baseUnitToInvariantUnit K L (invariantUnitToBaseUnit K L x) = x := by
  apply Subtype.ext
  apply Additive.ofMul.injective
  ext
  exact invariantUnitToBaseUnit_spec K L x

/-- The canonical additive equivalence `(Lˣ)^Gal(L/K) ≃ Kˣ` for finite Galois extensions. -/
noncomputable def invariantsUnitsAddEquivBaseUnits (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    unitsInvariantSubmodule K L ≃+ Additive Kˣ where
  toFun := fun x => Additive.ofMul (invariantUnitToBaseUnit K L x)
  invFun := fun x => baseUnitToInvariantUnit K L (Additive.toMul x)
  left_inv := baseUnitToInvariantUnit_invariantUnitToBaseUnit K L
  right_inv := by
    intro x
    apply Additive.ofMul.injective
    exact invariantUnitToBaseUnit_baseUnitToInvariantUnit K L (Additive.toMul x)
  map_add' := by
    intro x y
    apply Additive.ofMul.injective
    change
      invariantUnitToBaseUnit K L (x + y) =
        invariantUnitToBaseUnit K L x * invariantUnitToBaseUnit K L y
    ext
    apply FaithfulSMul.algebraMap_injective K L
    change
      algebraMap K L (invariantUnitToBaseUnit K L (x + y) : K) =
        algebraMap K L
          ((invariantUnitToBaseUnit K L x : K) *
            (invariantUnitToBaseUnit K L y : K))
    rw [map_mul, invariantUnitToBaseUnit_spec,
      invariantUnitToBaseUnit_spec, invariantUnitToBaseUnit_spec]
    rfl

/-- The canonical linear equivalence `(Lˣ)^Gal(L/K) ≃ Kˣ` for finite Galois extensions. -/
noncomputable def invariantsUnitsEquivBaseUnits (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    unitsInvariantSubmodule K L ≃ₗ[ℤ] Additive Kˣ :=
  (invariantsUnitsAddEquivBaseUnits K L).toIntLinearEquiv

/-- Restricting an invariant unit and re-embedding its value recovers the
underlying extension-field unit. -/
lemma invariantsUnitsAddEquivBaseUnits_spec (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    algebraMap K L
        ((Additive.toMul (invariantsUnitsAddEquivBaseUnits K L x) : Kˣ) : K) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) := by
  exact invariantUnitToBaseUnit_spec K L x

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_NormImage
attribute [-instance] _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.TateH0.NormImage` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory
open CategoryTheory

noncomputable section

universe u

/-- The group-cohomological norm endomorphism on the actual unit representation. -/
def unitsNormLinearMap (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Additive Lˣ →ₗ[ℤ] Additive Lˣ :=
  (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap

/-- The additive unit norm is fixed by the Galois action. -/
lemma unitsNorm_mem_invariants (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] (x : Additive Lˣ) :
    unitsNormLinearMap K L x ∈ unitsInvariantSubmodule K L := by
  intro σ
  exact Representation.self_norm_apply (Rep.ofAlgebraAutOnUnits K L).ρ σ x

/-- The norm map, codomain-restricted to invariant units. -/
def unitsNormToInvariantsLinearMap (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Additive Lˣ →ₗ[ℤ] unitsInvariantSubmodule K L :=
  (unitsNormLinearMap K L).codRestrict (unitsInvariantSubmodule K L)
    (unitsNorm_mem_invariants K L)

/-- Norm image inside invariant units. -/
def unitsTateH0NormSubmodule (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Submodule ℤ (unitsInvariantSubmodule K L) :=
  LinearMap.range (unitsNormToInvariantsLinearMap K L)

/-- The value of the additive unit norm map is the field norm of the underlying unit. -/
theorem unitsNormLinearMap_apply_val (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     (Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) : Lˣ).1) =
      algebraMap K L (Algebra.norm K (x : L)) := by
  let := AlgEquiv.fintype K L
  dsimp only [unitsNormLinearMap]
  change ((Additive.toMul
    ((Rep.ofAlgebraAutOnUnits K L).norm.hom (Additive.ofMul x)) : Lˣ).1) =
      algebraMap K L (Algebra.norm K (x : L))
  rw [← groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := K) (L := L) x]
  rfl

/-- A finite sum of additive units corresponds to the product of their underlying units. -/
@[simp]
lemma additive_toMul_finset_sum_units {ι : Type*} (L : Type*) [Field L]
    (s : Finset ι) (f : ι → Additive Lˣ) :
    Additive.toMul (Finset.sum s f) =
      Finset.prod s (fun i => Additive.toMul (f i)) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert, Finset.prod_insert, ha, hs]

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_SeparableNormValuation
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: normalized valuation of field norms

This file supplies the local-field calculation used when the abstract
class-formation framework is specialized to separable-closure units.  All
ramification and residue degrees below are the actual invariants of the
valuation-ring extension; no packaged norm-valuation hypothesis is assumed.
-/

noncomputable section

universe u v w

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField

section SeparableIdealNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/-- A normal closure inside a separable ambient field is separable over the
base whenever the extension being closed is separable.  Keeping this
field-theoretic step separate prevents the integral-closure transport below
from repeatedly elaborating the full `iSup` of embedding ranges. -/
theorem intermediateNormalClosure_isSeparable_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L A) := by
  change Algebra.IsSeparable K ↥(⨆ f : L →ₐ[K] A, f.fieldRange)
  exact IntermediateField.isSeparable_iSup K A
    (h := fun f => AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f))

/-- The field-theoretic normal closure of a finite separable extension is
Galois, with no perfectness assumption on the base. -/
theorem intermediateNormalClosure_isGalois_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Normal K A] :
    IsGalois K (IntermediateField.normalClosure K L A) := by
  exact
    { to_isSeparable :=
        intermediateNormalClosure_isSeparable_of_isSeparable K L A
      to_normal := normalClosure.normal K L A }

/-- A finite extension remains finite over the field-theoretic normal
closure when viewed from the top of the tower. -/
theorem intermediateNormalClosure_finiteDimensional_top
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L] :
    let E := IntermediateField.normalClosure K L A
    letI : Algebra L E := normalClosure.algebra K L A
    FiniteDimensional L E := by
  exact Module.Finite.right K L (IntermediateField.normalClosure K L A)

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] in
/-- The integral normal closure has the field-theoretic normal closure as
its fraction field. -/
theorem ringNormalClosure_isFractionRing :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra L E := normalClosure.algebra K L A
    letI : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
    letI : Algebra T E := by
      change Algebra (integralClosure S E) E
      infer_instance
    IsFractionRing T E := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  change IsFractionRing (integralClosure S E) E
  exact integralClosure.isFractionRing_of_finite_extension L E

omit [IsIntegrallyClosed R] [IsIntegrallyClosed S] in
/-- Transport Galoisness from the field-theoretic normal closure to the
fraction field of the integral normal closure. -/
theorem ringNormalClosure_isGalois_transport :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra K E := SubalgebraClass.toAlgebra E
    letI : Algebra K (FractionRing T) :=
      FractionRing.liftAlgebra R (FractionRing T)
    IsGalois K E → IsGalois K (FractionRing T) := by
  simp only
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
  let : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
  let : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  let : IsFractionRing T E := ringNormalClosure_isFractionRing R S
  intro hGalois
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

end SeparableIdealNorm

section SeparableIdealNormDedekind

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/-- The same separable normal-closure construction is Dedekind when the
original rings are Dedekind. -/
theorem ringNormalClosure_isDedekindDomain_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsDedekindDomain (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change IsDedekindDomain (integralClosure S E)
  exact integralClosure.isDedekindDomain S L E

end SeparableIdealNormDedekind

section SeparableIdealNormGalois

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/-- The normal closure of a finite separable extension of fraction fields is
Galois without assuming that the base fraction field is perfect.  Mathlib's
default instance uses perfectness because it treats arbitrary finite
extensions; here separability is precisely the available hypothesis. -/
theorem ringNormalClosure_isGalois_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsGalois (FractionRing R)
      (FractionRing (Ring.NormalClosure R S)) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let T := Ring.NormalClosure R S
  exact ringNormalClosure_isGalois_transport R S
    (intermediateNormalClosure_isGalois_of_isSeparable K L A)

end SeparableIdealNormGalois

attribute [local instance] FractionRing.liftAlgebra

/-- Separability of an actual field extension transfers to the canonical
fraction fields of its valuation integer rings. -/
theorem fractionRing_integerRing_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  apply Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
    (FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv
  ext x
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv 𝒪[K] K).symm
    (FractionRing.algEquiv 𝒪[L] L).symm x

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_ClosedAddSubgroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Closed additive subgroups of the p-adic integers

A nonzero closed additive subgroup of `ℤ_[p]` contains a nonzero principal
ideal.  Since every nonzero ideal of `ℤ_[p]` is generated by a power of `p`,
such a subgroup is open.
-/

open scoped Topology

namespace PadicInt

/-- A nonzero closed additive subgroup of the `p`-adic integers is open. -/
theorem addSubgroup_isOpen_of_isClosed_of_ne_bot
    (p : ℕ) [hp : Fact p.Prime]
    (H : AddSubgroup ℤ_[p])
    (hclosed : IsClosed (H : Set ℤ_[p]))
    (hne : H ≠ ⊥) :
    IsOpen (H : Set ℤ_[p]) := by
  obtain ⟨⟨x, hxH⟩, hx⟩ :=
    AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
  have hx0 : x ≠ 0 := fun h ↦ hx (Subtype.ext h)
  have hmul (a : ℤ_[p]) : x * a ∈ H := by
    refine PadicInt.denseRange_intCast.induction_on a ?_ ?_
    · change IsClosed ((fun y : ℤ_[p] ↦ x * y) ⁻¹' (H : Set ℤ_[p]))
      exact hclosed.preimage (continuous_const.mul continuous_id)
    · intro z
      simpa only [zsmul_eq_mul, mul_comm] using H.zsmul_mem hxH z
  have hspan_le :
      (Ideal.span ({x} : Set ℤ_[p])).toAddSubgroup ≤ H := by
    intro y hy
    change y ∈ Ideal.span ({x} : Set ℤ_[p]) at hy
    rw [Ideal.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    exact hmul a
  have hspan_ne :
      (Ideal.span ({x} : Set ℤ_[p]) : Ideal ℤ_[p]) ≠ ⊥ := by
    intro hzero
    have hxmem :
        x ∈ (Ideal.span ({x} : Set ℤ_[p]) : Ideal ℤ_[p]) :=
      Ideal.subset_span (by simp)
    rw [hzero] at hxmem
    exact hx0 (by simpa using hxmem)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hspan_ne
  have hpow_open :
      IsOpen
        ((Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p]) :
            Ideal ℤ_[p]) :
          Set ℤ_[p]) := by
    have hset :
        ((Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p]) :
            Ideal ℤ_[p]) :
          Set ℤ_[p]) =
          Metric.closedBall 0 ((p : ℝ) ^ (-n : ℤ)) := by
      ext y
      change y ∈
          (Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p]) :
            Ideal ℤ_[p]) ↔
        dist y 0 ≤ (p : ℝ) ^ (-n : ℤ)
      rw [dist_zero_right,
        PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [hset]
    exact IsUltrametricDist.isOpen_closedBall
      (0 : ℤ_[p]) (by
        apply zpow_ne_zero
        exact_mod_cast hp.out.ne_zero)
  have hspan_open :
      IsOpen
        ((Ideal.span ({x} : Set ℤ_[p]) : Ideal ℤ_[p]) :
          Set ℤ_[p]) := by
    rw [hn]
    exact hpow_open
  exact AddSubgroup.isOpen_mono hspan_le hspan_open

end PadicInt
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace

open Filter Set Topology

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped Matrix
open Matrix



def columnModule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.range A.mulVecLin

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerPrimeProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime decomposition of the profinite integers

This file constructs the canonical map
`ℤ̂ → ∏ p : Nat.Primes, ℤ_p` from the compatible finite reductions.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

local instance instFactPrimeValNat_solutions (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The product of the additive rings of `p`-adic integers over all
rational primes. -/
abbrev ProfiniteIntegerPrimeProduct :=
  ∀ p : Nat.Primes, ℤ_[p.1]

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Units of the profinite integers

This file upgrades the prime-product Chinese-remainder equivalence for
`ℤ̂` to topological additive, multiplicative, and unit-group equivalences.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

local instance instFactPrimeValNat_solutions_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end ClassFormation
end
end


