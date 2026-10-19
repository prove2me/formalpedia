-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
-- name    : OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:39:31.427533+00:00
-- url     : https://prove2.me/theorems/380b3fc2-a3a7-4aa6-8e29-a4cbaebcf4ca
-- title:
--   Association by a unit with residue one
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Residue-one association.** For a ring homomorphism $\mathrm{res}:S\to k$, elements $x,y\in S$ are associated with residue one if
--   $$
--   x=w\,y\quad\text{for a unit }w\text{ with }\mathrm{res}(w)=1.
--   $$
--   This relation is reflexive, symmetric and transitive, and the inverse of such a unit again has residue one. For a local ring the residue map is the quotient by its maximal ideal. The relation states the conclusion of the local comparison without dividing in the coefficient ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/ResidueOneAssociation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/ResidueOneAssociation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CirculantHadamard mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily

namespace OAI

universe uS uk

/-!
# Association by a unit with residue one

This algebraic relation expresses the local comparison conclusion without
introducing division in the coefficient ring. The scalar-cancellation lemmas
require regularity explicitly; they do not give group rings a domain instance.
For a local ring, the residue map is the quotient by its maximal ideal.
-/

namespace CirculantHadamard.LocalComparison

variable {S : Type uS} {k : Type uk} [CommRing S] [CommRing k]

/-- `x` differs from `y` by multiplication by a unit whose residue is one. -/
def ResidueOneAssociated (residue : S →+* k) (x y : S) : Prop :=
  ∃ u : Sˣ, x = (u : S) * y ∧ residue (u : S) = 1

theorem residue_inv_eq_one (residue : S →+* k) {u : Sˣ}
    (hu : residue (u : S) = 1) : residue (↑u⁻¹ : S) = 1 := by
  have h : residue (u : S) * residue (↑u⁻¹ : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simpa only [hu, one_mul] using h

namespace ResidueOneAssociated

variable {residue : S →+* k} {x y z c x' y' : S}

@[refl] theorem refl (residue : S →+* k) (x : S) :
    ResidueOneAssociated residue x x := by
  exact ⟨1, by simp, by simp⟩

@[symm] theorem symm (h : ResidueOneAssociated residue x y) :
    ResidueOneAssociated residue y x := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [hxy, Units.inv_mul_cancel_left]

@[trans] theorem trans (hxy : ResidueOneAssociated residue x y)
    (hyz : ResidueOneAssociated residue y z) : ResidueOneAssociated residue x z := by
  obtain ⟨u, hxy, hu⟩ := hxy
  obtain ⟨v, hyz, hv⟩ := hyz
  refine ⟨u * v, ?_, ?_⟩
  · simp only [Units.val_mul, hxy, hyz, mul_assoc]
  · simp only [Units.val_mul, map_mul, hu, hv, one_mul]

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI


