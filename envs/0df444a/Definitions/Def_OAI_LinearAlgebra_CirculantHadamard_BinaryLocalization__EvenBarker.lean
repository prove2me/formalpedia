-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:30:41.575384+00:00
-- url     : https://prove2.me/theorems/b1f94614-1f0e-4a5b-9166-95218e635b65
-- title:
--   Maximal ideals over two and units from odd norms
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **A maximal ideal over $2$.** A characteristic-zero ring that is a finitely generated $\mathbb Z$-module has a maximal ideal containing $2$.
--   2. **Residue characteristic.** If a prime ideal $\mathfrak m$ contains $2$, the residue field of the localization at $\mathfrak m$ has characteristic $2$; in such a field every odd integer maps to $1$.
--   3. **Units from odd norms.** In a local ring with residue characteristic $2$, if $xy=u^2$ for an odd integer $u$, then $x$ is a unit:
--   $$
--   xy=u^2,\ u\text{ odd}\ \Longrightarrow\ x\in O^{\times},
--   $$
--   because $u^2$ maps to $1$ in the residue field. No conjugation on the local ring is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalization.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalization.lean by skeleton subtraction
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

namespace OAI

universe uB uO uk uF

/-!
# The characteristic-two local ring for the binary contradiction

The maximal ideal is constructed from an actual finite characteristic-zero
integer algebra.  Unit denominators follow from the odd norm identity, not
from an assumed extension of complex conjugation to a localization.
-/

namespace CirculantHadamard.BinaryLocalization

/-- A finite characteristic-zero integer algebra has a maximal ideal over two. -/
theorem exists_maximal_two_mem (B : Type uB) [CommRing B] [CharZero B]
    [Module.Finite ℤ B] :
    ∃ m : Ideal B, m.IsMaximal ∧ (2 : B) ∈ m := by
  let : Algebra.IsIntegral ℤ B := Algebra.IsIntegral.of_finite ℤ B
  obtain ⟨m, hm, _, htwo⟩ :=
    exists_maximal_ideal_over_nat_prime_of_charZero B Nat.prime_two
  exact ⟨m, hm, htwo⟩

/-- The one residue field used by both first-order maps has characteristic two. -/
theorem residue_char_two {B : Type uB} [CommRing B] (m : Ideal B) [m.IsPrime]
    (htwo : (2 : B) ∈ m) :
    CharP (IsLocalRing.ResidueField (Localization.AtPrime m)) 2 := by
  let O := Localization.AtPrime m
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have hmem : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (2 : B)).mpr htwo
  have hz := (IsLocalRing.residue_eq_zero_iff (2 : O)).mpr hmem
  simpa only [map_ofNat] using hz

/-- An odd scalar is one in the common characteristic-two residue field. -/
theorem map_odd_nat_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) {u : ℕ} (hu : Odd u) : φ (u : O) = 1 := by
  rw [map_natCast]
  exact natCast_eq_one_of_odd_of_two_eq_zero hu CharTwo.two_eq_zero

/-- The odd norm supplies a unit without requiring the second factor to be a
conjugation operation on the local ring. -/
theorem isUnit_of_mul_eq_odd_square {O : Type uO} [CommRing O] [IsLocalRing O]
    [CharP (IsLocalRing.ResidueField O) 2] {x y : O} {u : ℕ}
    (hu : Odd u) (hxy : x * y = (u : O) ^ 2) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro hx
  have h := congrArg (IsLocalRing.residue O) hxy
  have hu' := map_odd_nat_eq_one (IsLocalRing.residue O) hu
  have hbad : (0 : IsLocalRing.ResidueField O) = 1 := by
    simpa only [map_mul, map_pow, hx, zero_mul, hu', one_pow] using h
  exact zero_ne_one hbad

end CirculantHadamard.BinaryLocalization

end OAI


