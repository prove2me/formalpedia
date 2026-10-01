-- Prove2me | Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
-- name    : LocalConjugacy_Proof_ConcreteGroups
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:10:15.311776+00:00
-- url     : https://prove2.me/theorems/15fc6ff4-252d-4418-8102-8f1796fb82e5
-- title:
--   Explicit identifications of the finite example groups
-- statement:
--   The equivalence $D_6\cong S_3$, the induced wreath-product equivalence, Heisenberg coordinates on the normal subgroup of order $27$, the cyclic group of order $6$, and the product description of the stabilizer. The finite formulas are checked by kernel reduction.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable

/-! Supporting definitions and the structural proofs required by their types and values. -/

section


/-!
Explicit identifications for the counterexamples.  The formulas specify the
isomorphisms, and all finite certificates below are checked by Lean's kernel
with `decide`.  No native evaluator or additional axiom is used.
-/
namespace LocalConjugacy
namespace Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The usual faithful action of the dihedral group of order six on three
letters: rotations translate and reflections negate after translating. -/
def dihedralPermutation : DihedralGroup 3 →* S3 where
  toFun s :=
    { toFun := LocalConjugacy.HeisenbergExample.perm s
      invFun := LocalConjugacy.HeisenbergExample.perm s⁻¹
      left_inv := by
        intro i
        exact (show ∀ z : ZMod 3, LocalConjugacy.HeisenbergExample.perm s⁻¹
          (LocalConjugacy.HeisenbergExample.perm s z) = z from by
            intro z
            rw [← LocalConjugacy.HeisenbergExample.perm_mul, inv_mul_cancel,
              LocalConjugacy.HeisenbergExample.perm_one]) i
      right_inv := by
        intro i
        exact (show ∀ z : ZMod 3, LocalConjugacy.HeisenbergExample.perm s
          (LocalConjugacy.HeisenbergExample.perm s⁻¹ z) = z from by
            intro z
            rw [← LocalConjugacy.HeisenbergExample.perm_mul, mul_inv_cancel,
              LocalConjugacy.HeisenbergExample.perm_one]) i }
  map_one' := by apply Equiv.ext; intro i; exact LocalConjugacy.HeisenbergExample.perm_one i
  map_mul' s t := by apply Equiv.ext; intro i; exact LocalConjugacy.HeisenbergExample.perm_mul s t i



/-- Read a permutation from the images of zero and one. This explicit inverse
keeps the counterexample's transported action computational. -/
def permutationDihedral (s : S3) : DihedralGroup 3 :=
  let a : ZMod 3 := s 0
  let b : ZMod 3 := s 1
  if b = a + 1 then .r a else .sr (-a)

/-- Mathlib's dihedral and symmetric models of S₃ are isomorphic. -/
def dihedralEquiv : DihedralGroup 3 ≃* S3 where
  toFun := dihedralPermutation
  invFun := permutationDihedral
  left_inv := by decide
  right_inv := by decide
  map_mul' := dihedralPermutation.map_mul

/-- The existing nine-point example is the natural imprimitive wreath product.
The base is unchanged; only the presentation of the permutation group changes. -/
noncomputable def wreathEquiv : LocalConjugacy.HeisenbergExample.G ≃* WreathC3S3 :=
  SemidirectProduct.congr (MulEquiv.refl _) dihedralEquiv (by
    intro s
    ext b i
    rfl)

-- Finite coordinates make the matrix model available to exhaustive kernel checks.
deriving instance DecidableEq, Fintype for Heisenberg3

/-- In the sum-zero base, write the vector as `c - b*i` and use rotation `a`.
Rotating the next vector adds exactly the cross term `a*b'`, giving the
upper-unitriangular Heisenberg multiplication law. -/
def heisenbergCoordinates : Heisenberg3 →* LocalConjugacy.HeisenbergExample.G where
  toFun x := ⟨fun i => Multiplicative.ofAdd (x.c - x.b * i), .r x.a⟩
  map_one' := by decide
  map_mul' := by decide

/-- The coordinate vectors have sum zero and the permutations have even sign. -/
def heisenbergKernelCoordinates : Heisenberg3 →* LocalConjugacy.HeisenbergExample.N :=
  heisenbergCoordinates.codRestrict _ (by decide)

/-- Each of the 27 kernel elements has a unique Heisenberg coordinate triple. -/
theorem heisenbergKernelCoordinates_bijective :
    Function.Bijective heisenbergKernelCoordinates := by
  constructor
  · exact (by decide : ∀ x y,
      heisenbergKernelCoordinates x = heisenbergKernelCoordinates y → x = y)
  · exact (by decide : ∀ y, ∃ x, heisenbergKernelCoordinates x = y)

/-- Identification of the actual normal subgroup with the named matrix group. -/
noncomputable def heisenbergEquiv : LocalConjugacy.HeisenbergExample.N ≃* Heisenberg3 :=
  (MulEquiv.ofBijective heisenbergKernelCoordinates
    heisenbergKernelCoordinates_bijective).symm

/-- The explicit cyclic complement has order six, hence is Mathlib's C₆. -/
noncomputable def cyclicSixEquiv :
    LocalConjugacy.HeisenbergExample.J ≃* Multiplicative (ZMod 6) := by
  have e := (zmodCyclicMulEquiv LocalConjugacy.HeisenbergExample.cyclic_J).symm
  have hc : Nat.card LocalConjugacy.HeisenbergExample.J = 6 := by
    simpa [Nat.card_eq_fintype_card] using LocalConjugacy.HeisenbergExample.card_J
  rw [hc] at e
  exact e

/-- The stabilizer coordinates split into a diagonal C₃ and a symmetric factor. -/
noncomputable def stabilizerProductEquiv :
    LocalConjugacy.HeisenbergExample.H ≃* C3 × S3 :=
  LocalConjugacy.HeisenbergExample.hEquivProduct.trans
    (MulEquiv.prodCongr (MulEquiv.refl C3) dihedralEquiv)

end Proof
end LocalConjugacy

end


