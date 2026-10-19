-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:28:11.728224+00:00
-- url     : https://prove2.me/theorems/0fb0cc5f-1fc4-4cac-8a23-a0b2fdc5fcc6
-- title:
--   The local ring of the cyclotomic coefficient ring at a prime over two
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Fix an odd $u$ and the ring $B_u=\mathbb Z[i,\rho_q:q\mid u]\subseteq\mathbb C$.
--
--   1. **Prime over two.** A chosen maximal ideal $\mathfrak m_u$ of $B_u$ containing $2$, depending only on $u$.
--   2. **Local ring and residue field.** $O_u=(B_u)_{\mathfrak m_u}$, with residue field $k_u$ of characteristic $2$; $O_u$ has characteristic zero.
--   3. **Maps.** The injective localization map $B_u\to O_u$, the map $O_u\to\operatorname{Frac}(B_u)$ compatible with $B_u\to\operatorname{Frac}(B_u)$, the residue map $O_u\to k_u$, the Gaussian integers into $O_u$, and the image of $i$ in $O_u$.
--   4. **Norm units.** If $x,y\in B_u$ satisfy $xy=u^2$, the image of $x$ in $O_u$ is a unit, recorded with its actual value:
--   $$
--   x\in B_u,\ xy=u^2\ \Longrightarrow\ x\in O_u^{\times}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalRing.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalRing.lean by skeleton subtraction
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

namespace OAI

/-!
# One concrete local ring and residue field

For the actual cyclotomic coefficient algebra `B u`, choose a maximal ideal
containing two. Both first-order calculations use the same localization and
the same residue field. The choices depend only on `u`, not on a character or
on which of the three norm elements is being considered.
-/

noncomputable section

namespace CirculantHadamard.BinaryLocalRing

open CyclotomicRings

def twoIdeal (u : ℕ) : Ideal (B u) :=
  Classical.choose (BinaryLocalization.exists_maximal_two_mem (B u))

instance twoIdeal_isMaximal (u : ℕ) : (twoIdeal u).IsMaximal :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).1

theorem two_mem (u : ℕ) : (2 : B u) ∈ twoIdeal u :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).2

abbrev O (u : ℕ) := Localization.AtPrime (twoIdeal u)

/- Name the canonical localization algebra directly. This avoids searching
through iterated-localization algebra instances for these concrete carriers. -/
instance local_algebra (u : ℕ) : Algebra (B u) (O u) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := (twoIdeal u).primeCompl)

instance fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

abbrev k (u : ℕ) := IsLocalRing.ResidueField (O u)

def toLocal (u : ℕ) : B u →+* O u := algebraMap (B u) (O u)

theorem toLocal_injective (u : ℕ) : Function.Injective (toLocal u) :=
  IsLocalization.injective (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

/-- The same localization embeds into the fraction field used for the
alternating products. -/
def toFraction (u : ℕ) : O u →ₐ[B u] FractionRing (B u) :=
  Localization.mapToFractionRing (FractionRing (B u)) (twoIdeal u).primeCompl
    (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

@[simp] theorem toFraction_toLocal (u : ℕ) (x : B u) :
    toFraction u (toLocal u x) = algebraMap (B u) (FractionRing (B u)) x :=
  (toFraction u).commutes x

instance local_charZero (u : ℕ) : CharZero (O u) where
  cast_injective a b hab := by
    apply (Nat.cast_injective (R := B u))
    apply toLocal_injective u
    simpa only [map_natCast] using hab

instance residue_charTwo (u : ℕ) : CharP (k u) 2 :=
  BinaryLocalization.residue_char_two (twoIdeal u) (two_mem u)

def residue (u : ℕ) : O u →+* k u := IsLocalRing.residue (O u)

def gaussianToLocal (u : ℕ) : GaussianRing →+* O u :=
  (toLocal u).comp (gaussianToB u).toRingHom

def imaginary (u : ℕ) : O u := gaussianToLocal u gaussianI

/-- Every one of the actual character norms supplies its own local unit. -/
theorem norm_isUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : IsUnit (toLocal u x) := by
  apply BinaryLocalization.isUnit_of_mul_eq_odd_square hu
    (y := toLocal u y)
  have h := congrArg (toLocal u) hxy
  simpa only [map_mul, map_pow, map_natCast] using h

/-- The unit value is the localized character value, not an unrelated witness. -/
def normUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : (O u)ˣ :=
  (norm_isUnit u hu x y hxy).unit

@[simp] theorem normUnit_val (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) :
    (normUnit u hu x y hxy : O u) = toLocal u x :=
  (norm_isUnit u hu x y hxy).unit_spec

end CirculantHadamard.BinaryLocalRing

end

end OAI


