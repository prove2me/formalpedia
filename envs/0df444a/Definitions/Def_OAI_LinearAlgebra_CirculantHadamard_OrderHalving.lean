-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
-- name    : OAI_LinearAlgebra_CirculantHadamard_OrderHalving
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:07:13.90205+00:00
-- url     : https://prove2.me/theorems/ea84a97e-24e6-43da-8646-1566c5dfb892
-- title:
--   Halving paired coefficients over a cyclic quotient
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Pair average.** For integers $a,b$, the integer $\lfloor(a+b)/2\rfloor$, used only when $a+b$ is even.
--   2. **Halving map.** For $m>0$ and $T\in\mathbb Z[\mathbb Z/2m]$, the element of $\mathbb Z[\mathbb Z/m]$ whose coefficient at $j\in\{0,\dots,m-1\}$ is
--   $$
--   \frac{T(j)+T(j+m)}{2}.
--   $$
--   The numerator is the coefficient of the projection of $T$ to $\mathbb Z[\mathbb Z/m]$ at $j$, so halving divides that projection by $2$ once its coefficients are known to be even.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderHalving.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderHalving.lean by skeleton subtraction
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

namespace OAI

/-!
# Halving an odd-coefficient dyadic group-ring element

The integer averaging lemmas retain the original paired coefficients.
The group-ring step uses their actual quotient fiber sums and the concrete
cyclotomic divisibility theorem; the ring is not assumed to be a domain.
-/

namespace CirculantHadamard

open CyclicRing

/-- The coefficient obtained by projecting a pair and dividing by two. -/
def pairAverage (a b : ℤ) : ℤ := (a + b) / 2

/-- Literal paired coefficients on the quotient of a cyclic group of even
order. Integer divisibility is proved separately before this is used. -/
noncomputable def halvePairs {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m)) : Elem ℤ m :=
  ofCoeffs fun j => pairAverage (T.coeff (j.val : ZMod (2 * m)))
    (T.coeff ((j.val + m : ℕ) : ZMod (2 * m)))

@[simp] theorem halvePairs_apply {m : ℕ} [NeZero m] (T : Elem ℤ (2 * m))
    (j : ZMod m) :
    (halvePairs T).coeff j = pairAverage (T.coeff (j.val : ZMod (2 * m)))
      (T.coeff ((j.val + m : ℕ) : ZMod (2 * m))) := rfl

end CirculantHadamard

end OAI


