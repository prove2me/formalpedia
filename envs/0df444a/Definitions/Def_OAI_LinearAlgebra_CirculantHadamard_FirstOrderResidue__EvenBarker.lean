-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:39:38.109567+00:00
-- url     : https://prove2.me/theorems/3a01954c-c5f7-4c16-89db-b0c9512b9e3f
-- title:
--   Principal units and their first-order residue homomorphism
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Let $O$ be a commutative ring and $t\in O$.
--
--   1. **Principal units.** The subgroup of units of the form $1+ta$ with $a\in O$.
--   2. **Coefficient.** A chosen $a$ with $u=1+ta$. If $O$ is a domain and $t\ne0$ it is unique, and
--   $$
--   a(uv)=a(u)+a(v)+t\,a(u)\,a(v).
--   $$
--   3. **First-order homomorphism.** For a ring homomorphism $\varphi:O\to K$ into a field with $\varphi(t)=0$, the map $u\mapsto\varphi(a(u))$ from the principal units to the additive group of $K$. It is a group homomorphism because the cross term $t\,a(u)a(v)$ is killed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/FirstOrderResidue.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/FirstOrderResidue.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport__EvenBarker

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uO uK uIota

/-!
# First-order residues of principal units

For a nonzero element `t` of a domain, a unit of the form `1 + t * a` has a
unique coefficient `a`. A ring homomorphism killing `t` sends the coefficient
of a product to the sum of the coefficients. This constructs the actual
first-order homomorphism without identifying any quotient rings.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- Units whose difference from one is a multiple of the specified element. -/
def principalUnits (t : O) : Subgroup Oˣ where
  carrier := {u | ∃ a : O, (u : O) = 1 + t * a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b + t * a * b, ?_⟩
    change (u : O) * (v : O) = _
    rw [ha, hb]
    ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-a * (↑u⁻¹ : O), ?_⟩
    have h := u.mul_inv
    rw [ha] at h
    linear_combination h

@[simp]
theorem mem_principalUnits (t : O) (u : Oˣ) :
    u ∈ principalUnits t ↔ ∃ a : O, (u : O) = 1 + t * a :=
  Iff.rfl

/-- The coefficient of a principal unit. Its uniqueness is proved separately
using the domain assumption and `t ≠ 0`. -/
noncomputable def principalUnitCoeff (t : O) (u : principalUnits t) : O :=
  Classical.choose u.property

theorem principalUnitCoeff_spec (t : O) (u : principalUnits t) :
    ((u : Oˣ) : O) = 1 + t * principalUnitCoeff t u :=
  Classical.choose_spec u.property

section Domain

variable [IsDomain O]

theorem principalUnitCoeff_eq (t : O) (ht : t ≠ 0) (u : principalUnits t)
    {a : O} (ha : ((u : Oˣ) : O) = 1 + t * a) :
    principalUnitCoeff t u = a := by
  apply mul_left_cancel₀ ht
  exact add_left_cancel ((principalUnitCoeff_spec t u).symm.trans ha)

theorem principalUnitCoeff_mul (t : O) (ht : t ≠ 0)
    (u v : principalUnits t) :
    principalUnitCoeff t (u * v) =
      principalUnitCoeff t u + principalUnitCoeff t v +
        t * principalUnitCoeff t u * principalUnitCoeff t v := by
  apply principalUnitCoeff_eq t ht
  change ((u : Oˣ) : O) * ((v : Oˣ) : O) = _
  rw [principalUnitCoeff_spec, principalUnitCoeff_spec]
  ring

variable {K : Type uK} [Field K]

/-- The actual first-order homomorphism associated with a nonzero element
killed by the given residue map. `Multiplicative K` uses addition in `K`. -/
noncomputable def actualFirstOrder (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) : principalUnits t →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (φ (principalUnitCoeff t u))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t 1) = 0
    rw [principalUnitCoeff_eq t ht 1 (a := 0) (by simp), map_zero]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t (u * v)) =
      φ (principalUnitCoeff t u) + φ (principalUnitCoeff t v)
    rw [principalUnitCoeff_mul t ht]
    simp [hφt]

end Domain

end CirculantHadamard

end OAI


