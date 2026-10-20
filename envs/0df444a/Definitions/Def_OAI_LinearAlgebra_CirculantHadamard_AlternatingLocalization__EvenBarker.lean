-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:10:33.72279+00:00
-- url     : https://prove2.me/theorems/5436359d-4c6d-43fe-9293-fa3dc0118770
-- title:
--   Maximal localizations and the cyclotomic comparison map
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Maximal localizations.** For a commutative ring $R$ and a maximal ideal $\mathfrak m$, the localization $R_{\mathfrak m}$; if $R$ is a domain with fraction field $K$, the canonical embedding $R_{\mathfrak m}\to K$.
--   2. **Base localization.** For $f:A_0\to R$, the localization of $A_0$ at $f^{-1}(\mathfrak m)$ and the induced map to $R_{\mathfrak m}$, which agrees with $f$ on $A_0$.
--   3. **Comparison map.** If $\rho\in R$ is a root of $\Phi_p$, the ring homomorphism
--   $$
--   \bigl(A_0\bigr)_{f^{-1}(\mathfrak m)}[X]/(\Phi_p(X))\longrightarrow R_{\mathfrak m},\qquad X\mapsto\rho,
--   $$
--   given by the universal property of the quotient. The concrete localizations of $B_u$ at its maximal ideals and its fraction field are fixed as algebras. An element of the fraction field lying in every maximal localization lies in the base ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean by skeleton subtraction
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation__EvenBarker

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR uK uAZero uS uL uI uk

/-!
# Local representatives of the fixed alternating product

All local rings are actual localizations at maximal ideals. Their maps
into the common fraction field are canonical. The adjoined-root comparison
map is constructed from the actual base-ring inclusion and cyclotomic relation.
Membership in every maximal localization implies membership in the base ring.
-/

noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

abbrev AtMaximal (R : Type uR) [CommRing R] (m : MaximalSpectrum R) :=
  Localization.AtPrime m.asIdeal

def toFraction {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : AtMaximal R m →ₐ[R] K :=
  Localization.mapToFractionRing K m.asIdeal.primeCompl (AtMaximal R m)
    m.asIdeal.primeCompl_le_nonZeroDivisors

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- The actual coefficient localization at the contracted prime. Maximality
of the contraction is a separate input to the local comparison theorem, not
an assumption needed to construct this map. -/
abbrev AtComap (f : A₀ →+* R) (m : MaximalSpectrum R) :=
  Localization.AtPrime (m.asIdeal.comap f)

def baseToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) :
    AtComap f m →+* AtMaximal R m :=
  localizationAtComapMap f m.asIdeal

@[simp] theorem baseToLocal_algebraMap (f : A₀ →+* R) (m : MaximalSpectrum R)
    (a : A₀) :
    baseToLocal f m (algebraMap A₀ (AtComap f m) a) =
      algebraMap R (AtMaximal R m) (f a) :=
  localizationAtComapMap_algebraMap f m.asIdeal a

/-- The comparison algebra is mapped by the universal property of its actual
cyclotomic quotient, rather than by assuming an arbitrary extension map. -/
def comparisonToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) (p : ℕ) (rho : R)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    AdjoinRoot (Polynomial.cyclotomic p (AtComap f m)) →+* AtMaximal R m :=
  AdjoinRoot.lift (baseToLocal f m) (algebraMap R (AtMaximal R m) rho) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      Polynomial.cyclotomic.eval_apply, hroot, map_zero])

@[simp] theorem comparisonToLocal_root (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.root (Polynomial.cyclotomic p (AtComap f m))) =
      algebraMap R (AtMaximal R m) rho :=
  AdjoinRoot.lift_root _

@[simp] theorem comparisonToLocal_of (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (a : AtComap f m) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.of (Polynomial.cyclotomic p (AtComap f m)) a) =
      baseToLocal f m a :=
  AdjoinRoot.lift_of _

end ActualComparisonMap

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

end MaximalCover

section ConcreteComparison

open CyclicRing

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

/-- Name the canonical algebra structures directly to avoid searching through
iterated-localization algebra instances for the concrete coefficient ring. -/
instance B_local_algebra (u : ℕ) (m : MaximalSpectrum (B u)) :
    Algebra (B u) (AtMaximal (B u) m) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := m.asIdeal.primeCompl)

instance B_fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI


