-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
-- name    : OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:11:47.811981+00:00
-- url     : https://prove2.me/theorems/ed7f0d9c-d1b7-46bc-851b-c253a57fe441
-- title:
--   Half sums and half differences of four sign blocks
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   Let $H_0,H_1,H_2,H_3$ be integer-valued functions on a finite group $G$; they satisfy the sign condition when every value is $\pm1$.
--
--   1. **Integer halves.** $\mathrm{hs}(x,y)=(x+y)/2$, $\mathrm{hd}(x,y)=(x-y)/2$ and $\mathrm{off}(x)=(x-1)/2$, which are exact integers when $x,y$ are signs; then $x=1+2\,\mathrm{off}(x)$.
--   2. **The blocks $a,b,c,d$.** Pointwise $a=\mathrm{hs}(H_0,H_2)$, $b=\mathrm{hs}(H_1,H_3)$, and
--   $$
--   c=a+b,\qquad d=a-b.
--   $$
--   3. **The Gaussian combinations.** With integer real and imaginary parts placed in any commutative ring with a chosen element $i$: $g=\mathrm{hd}(H_0,H_2)+i\,\mathrm{hd}(H_1,H_3)$ and $U=\mathrm{off}(H_2)+i\,\mathrm{off}(H_3)$.
--   4. **All-ones element.** $J$, the function equal to $1$ at every group element (the sum of all group elements, not the unit of the convolution ring).
--   5. **Coefficient maps.** The integer coefficients of an element can be cast into any ring, in particular into $\mathbb C$, without changing the index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryCoefficients.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryCoefficients.lean by skeleton subtraction
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

namespace OAI

universe uG uR

namespace CirculantHadamard
namespace BinaryCoefficients

def halfSum (x y : ℤ) : ℤ := (x + y) / 2

def halfDiff (x y : ℤ) : ℤ := (x - y) / 2

def signOffset (x : ℤ) : ℤ := (x - 1) / 2

variable {G : Type uG}

/-- The canonical coefficient map, with no change to the index. -/
noncomputable def castCoeffs {R : Type uR} [Ring R] (f : G →₀ ℤ) : G →₀ R :=
  Finsupp.mapRange (fun z : ℤ => (z : R)) (by simp) f

@[simp] theorem castCoeffs_apply {R : Type uR} [Ring R] (f : G →₀ ℤ) (x : G) :
    castCoeffs (R := R) f x = (f x : R) := rfl

noncomputable def complexify (f : G →₀ ℤ) : G →₀ ℂ := castCoeffs f

@[simp] theorem complexify_apply (f : G →₀ ℤ) (x : G) :
    complexify f x = (f x : ℂ) := rfl

/-- Integer real and imaginary parts interpreted in any coefficient ring.
The linear identities do not require an equation such as `i^2 = -1`. -/
noncomputable def liftPair {R : Type uR} [CommRing R] (i : R) (f h : G →₀ ℤ) : G →₀ R :=
  castCoeffs f + i • castCoeffs h

variable [Finite G]

noncomputable def ofCoeffs {R : Type uR} [Zero R] (f : G → R) : G →₀ R :=
  Finsupp.equivFunOnFinite.symm f

@[simp] theorem ofCoeffs_apply {R : Type uR} [Zero R] (f : G → R) (x : G) :
    ofCoeffs f x = f x := rfl

/-- Literal sign hypotheses for the four blocks, without a norm premise. -/
def Signs (H : Fin 4 → (G →₀ ℤ)) : Prop := ∀ j x, IsSign (H j x)

noncomputable def a (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 0 x) (H 2 x)

noncomputable def b (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfSum (H 1 x) (H 3 x)

noncomputable def c (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H + b H

noncomputable def d (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ := a H - b H

noncomputable def gReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 0 x) (H 2 x)

noncomputable def gImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => halfDiff (H 1 x) (H 3 x)

noncomputable def gOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (gReal H) (gImag H)

noncomputable def UReal (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 2 x)

noncomputable def UImag (H : Fin 4 → (G →₀ ℤ)) : G →₀ ℤ :=
  ofCoeffs fun x => signOffset (H 3 x)

noncomputable def UOver {R : Type uR} [CommRing R] (i : R)
    (H : Fin 4 → (G →₀ ℤ)) : G →₀ R := liftPair i (UReal H) (UImag H)

/-- This is the sum of all group elements (every coefficient is one),
not the scalar one in a convolution ring. -/
noncomputable def JOver (R : Type uR) [CommRing R] : G →₀ R := ofCoeffs fun _ => 1

@[simp] theorem JOver_apply {R : Type uR} [CommRing R] (x : G) :
    (JOver R : G →₀ R) x = 1 := rfl

noncomputable def J : G →₀ ℂ := JOver ℂ

@[simp] theorem J_apply (x : G) : (J : G →₀ ℂ) x = 1 := rfl

end BinaryCoefficients
end CirculantHadamard

end OAI


