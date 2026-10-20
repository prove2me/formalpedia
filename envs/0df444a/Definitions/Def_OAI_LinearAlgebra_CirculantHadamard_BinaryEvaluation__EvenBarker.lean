-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:23:16.467926+00:00
-- url     : https://prove2.me/theorems/a0d7c5f6-1c7f-42ac-bfe4-4cb345015159
-- title:
--   Gaussian block elements and their character values
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   Let $H_0,\dots,H_3\in\mathbb Z[\mathbb Z/n]$ be four blocks, and let $a,b,c,d,g,U,J$ be the half-sum, half-difference and all-ones combinations of their coefficients.
--
--   1. **Gaussian elements.** The elements $a_G,b_G,c_G,d_G,g_G,U_G,J_G$ of $\mathbb Z[i][\mathbb Z/n]$ obtained by casting these integer coefficients into the Gaussian integers, with $i$ the Gaussian $i$ in $g$ and $U$; scalar multiplication by a Gaussian integer acts coefficientwise.
--   2. **Character values.** For odd $u>0$, $n=u^2$ and a set $S$ of primes dividing $u$, the values in $B_u$ obtained by applying the subset evaluation at $\chi_S$:
--   $$
--   a_S,\;b_S,\;c_S,\;d_S,\;g_S,\;U_S,\;J_S\in B_u,
--   $$
--   together with the element $i\in B_u$. These are the quantities compared in the binary contradiction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryEvaluation.lean by skeleton subtraction
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

namespace OAI

universe uR

/-!
# Evaluation of the actual binary coefficient construction

The integral `c,d` are mapped coefficientwise into the Gaussian subring, with
their proved convolution norms preserved. All values are taken by the
constructed prime-subset character map into the actual cyclotomic ring `B u`.
The norm equations follow from the original cyclic sign row.
-/

noncomputable section

namespace CirculantHadamard.BinaryEvaluation

open scoped BigOperators
open CyclicRing BinaryCoefficients CyclotomicRings PrimeComponents
open PrimeCharacterEvaluations

/- Select the canonical multiplication action directly. This avoids searching
through the concrete subalgebra's unrelated inherited scalar actions. -/
local instance gaussianSelfScalar : SMulZeroClass GaussianRing GaussianRing where
  smul r x := r * x
  smul_zero := mul_zero

local instance gaussianCoeffScalar (n : ℕ) :
    SMulZeroClass GaussianRing (ZMod n →₀ GaussianRing) := Finsupp.smulZeroClass

/-- The canonical coefficient action, with its group-algebra result type fixed. -/
def gaussianScale {n : ℕ} (r : GaussianRing) (x : Elem GaussianRing n) :
    Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff
    (@SMul.smul GaussianRing (ZMod n →₀ GaussianRing)
      (gaussianCoeffScalar n).toSMul r x.coeff)

@[simp] theorem gaussianScale_apply {n : ℕ} (r : GaussianRing)
    (x : Elem GaussianRing n) (a : ZMod n) : (gaussianScale r x).coeff a = r * x.coeff a := rfl

section CoefficientCast

variable {R : Type uR} [CommRing R] {n : ℕ} [NeZero n]

end CoefficientCast

section GaussianBlocks

variable {n : ℕ} [NeZero n]

def aG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (a (fun j => (H j).coeff)))
def bG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (b (fun j => (H j).coeff)))
def cG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (c (fun j => (H j).coeff)))
def dG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (castCoeffs (d (fun j => (H j).coeff)))
def gG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (gOver gaussianI (fun j => (H j).coeff))
def UG (H : Fin 4 → Elem ℤ n) : Elem GaussianRing n :=
  AddMonoidAlgebra.ofCoeff (UOver gaussianI (fun j => (H j).coeff))
def JG : Elem GaussianRing n := AddMonoidAlgebra.ofCoeff (JOver GaussianRing)

end GaussianBlocks

section Values

variable (u : ℕ) [NeZero u] (hu : 0 < u)

def iB : B u := gaussianToB u gaussianI

def aValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (aG H)
def bValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (bG H)
def cValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (cG H)
def dValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (dG H)
def gValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (gG H)
def UValue (H : Fin 4 → Elem ℤ (u ^ 2)) (S : Finset (PrimeIndex u)) : B u :=
  subsetEvaluation u hu S (UG H)
def JValue (S : Finset (PrimeIndex u)) : B u := subsetEvaluation u hu S JG

end Values

end CirculantHadamard.BinaryEvaluation

end

end OAI


