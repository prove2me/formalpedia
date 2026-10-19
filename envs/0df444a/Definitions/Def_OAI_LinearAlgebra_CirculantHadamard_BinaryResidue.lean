-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:35:57.068987+00:00
-- url     : https://prove2.me/theorems/53b886a3-c209-4490-ba1e-31ea5936bb56
-- title:
--   First-order coefficients of the binary ratios
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Let $O$ be a commutative ring with units $c$ and elements $b,J,U$ and $i$.
--
--   1. **Coefficient along $2$.** $L_r=-b\,c^{-1}$; when $c=a+b$ and $d=a-b$ it satisfies
--   $$
--   \frac dc=1+2L_r .
--   $$
--   2. **Coefficient along $1+i$.** $L_w=i\,b\,c^{-1}-J\,c^{-1}-(1-i)\,U\,c^{-1}$; when $g=a+ib-\bigl((1+i)J+2U\bigr)$ and $i^2=-1$ it gives $g/c=1+(1+i)L_w$.
--
--   These are the first-order residues of $d/c$ and $g/c$ used in characteristic two.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean by skeleton subtraction
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

namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- The coefficient of the ratio `d / c` along `2`. Division by `c` means
multiplication by the inverse of the supplied unit. -/
def binaryLr (c : Oˣ) (b : O) : O :=
  -b * (↑(c⁻¹) : O)

/-- The coefficient of the ratio `g / c` along `1 + i`. -/
def binaryLw (c : Oˣ) (i b J U : O) : O :=
  i * b * (↑(c⁻¹) : O) - J * (↑(c⁻¹) : O) -
    (1 - i) * U * (↑(c⁻¹) : O)

section Domain

variable [IsDomain O]

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

variable [IsDomain O]

end Residue

end CirculantHadamard

end OAI


