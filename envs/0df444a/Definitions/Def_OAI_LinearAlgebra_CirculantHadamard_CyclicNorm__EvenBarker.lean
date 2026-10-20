-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:42:16.901868+00:00
-- url     : https://prove2.me/theorems/8ef0e5fd-58f3-4bf2-b3da-a9569f4a65e2
-- title:
--   Sign rows as elements of the integer cyclic group ring
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Cyclic sign row.** An element $f\in\mathbb Z[\mathbb Z/n]$ is a cyclic sign row if every coefficient $f(a)$ is $1$ or $-1$.
--   2. **Row to group ring.** For $n>0$ and $h:\{0,\dots,n-1\}\to\mathbb Z$, the element of $\mathbb Z[\mathbb Z/n]$ whose coefficient at $a$ is $h$ evaluated at the representative of $a$ in $\{0,\dots,n-1\}$.
--   3. **Group ring to row.** Conversely, an element $f$ gives the integer row $j\mapsto f(j\bmod n)$. The two conversions are mutually inverse and keep the cyclic orientation, so integer first rows and elements of $\mathbb Z[\mathbb Z/n]$ are the same data.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicNorm.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicNorm.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every literal integer coefficient is a sign. -/
def CyclicSignRow {n : ℕ} (f : CyclicRing.Elem ℤ n) : Prop :=
  ∀ a, IsSign (f.coeff a)

section PositiveOrder

variable {n : ℕ} [NeZero n]

/-- The cyclic group-ring element whose coefficients are the given first row. -/
def cyclicRow (h : Fin n → ℤ) : CyclicRing.Elem ℤ n :=
  CyclicRing.ofCoeffs (fun a => h ((ZMod.finEquiv n).symm a))

/-- Recover the integer first row without changing the cyclic orientation. -/
def integerRow (f : CyclicRing.Elem ℤ n) : Fin n → ℤ :=
  fun j => f.coeff (ZMod.finEquiv n j)

@[simp] theorem cyclicRow_apply (h : Fin n → ℤ) (a : ZMod n) :
    (cyclicRow h).coeff a = h ((ZMod.finEquiv n).symm a) := by
  simp [cyclicRow]

@[simp] theorem integerRow_apply (f : CyclicRing.Elem ℤ n) (j : Fin n) :
    integerRow f j = f.coeff (ZMod.finEquiv n j) := rfl

@[simp] theorem cyclicRow_integerRow (f : CyclicRing.Elem ℤ n) :
    cyclicRow (integerRow f) = f := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  simp [integerRow]

@[simp] theorem integerRow_cyclicRow (h : Fin n → ℤ) :
    integerRow (cyclicRow h) = h := by
  funext j
  simp [integerRow]

end PositiveOrder

end CirculantHadamard

end

end OAI


