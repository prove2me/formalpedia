-- Prove2me | Definitions.Def_OneOfManyCC_Supplement_DeMorgan
-- name    : OneOfManyCC_Supplement_DeMorgan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:20:18.572646+00:00
-- url     : https://prove2.me/theorems/0f06e805-bb7d-4877-b30f-717baa920f51
-- title:
--   De Morgan formulas, their leaf count, and the formula measures $D(f)$ and $L(f)$ of a partial function
-- statement:
--   A **De Morgan formula** on the input bits $x_j$, $j\in\iota$, is a binary tree whose inner nodes are AND and OR gates and whose leaves are literals $x_j$, $\neg x_j$ or the constants $0$, $1$. Its **depth** is the maximum number of gates on a path from the root to a leaf, and its **leaf count** is the number of leaves, counted with multiplicity (constants included).
--
--   A **partial function** $f:\{0,1\}^\iota\to\{0,1,*\}$ is computed by a formula $\varphi$ if $\varphi$ is correct on the promise $f^{-1}(0)\cup f^{-1}(1)$:
--   $$\varphi(x)=f(x)\quad\text{whenever } f(x)\in\{0,1\}.$$
--   Then
--   $$D(f)=\min\{\operatorname{depth}(\varphi):\varphi\text{ computes }f\},\qquad L(f)=\min\{\operatorname{leaves}(\varphi):\varphi\text{ computes }f\}.$$
--   A total function $g$ is the partial function that never takes the value $*$.
--
--   These are the formula-depth and formula-size measures of Theorems 1.5, 1.6, 1.7 and 1.8.
--
--   **Formalization Note** A De Morgan formula is the mission's published `OneOfManyCC.Formula` over the leaf type `DMLeaf ι` (`lit j true` is $x_j$, `lit j false` is $\neg x_j$, `const b` is the constant $b$). A partial function is `(ι → Bool) → Option Bool` with `none` for $*$. The minima are `sInf` over `ℕ`; for finitely many input bits every partial function has a formula (a DNF), so the sets are nonempty and the minima are attained.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, pp.6–7 (PDF pp.7–8)

import Mathlib
import Definitions.Def_OneOfManyCC_Formula

namespace OneOfManyCC.Supplement

/-- **The leaves of a De Morgan formula**: literals `x_j`, `¬x_j` and the constants `0`, `1`.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.6:
"A De Morgan formula is a binary tree whose inner nodes are AND and OR gates and whose leaves
are literals xj and ¬xj or constants."

**Formalization Note.** A De Morgan formula on the input bits `ι` is the published
`OneOfManyCC.Formula (DMLeaf ι)` (AND/OR gates, depth = number of gates on a longest root–leaf path).
`lit j true` is `x_j`, `lit j false` is `¬x_j`, `const b` is the constant `b`. -/
inductive DMLeaf (ι : Type) : Type
  | lit (j : ι) (b : Bool) : DMLeaf ι
  | const (b : Bool) : DMLeaf ι

/-- The value of a De Morgan leaf at the input `x : ι → Bool`. -/
def dmVal {ι : Type} : DMLeaf ι → (ι → Bool) → Bool
  | DMLeaf.lit j b, x => if b then x j else !x j
  | DMLeaf.const b, _ => b

/-- The number of leaves of a formula, counted with multiplicity (constants included). -/
def leafCount {Λ : Type} : Formula Λ → ℕ
  | Formula.leaf _ => 1
  | Formula.and φ ψ => leafCount φ + leafCount ψ
  | Formula.or φ ψ => leafCount φ + leafCount ψ

/-- **A formula computes a partial function** (§3.1, pp.6–7): "A formula computes a partial function
f : {0, 1}ⁿ → {0, 1, ∗} if it is correct on the promise f⁻¹(0) ∪ f⁻¹(1)".

**Formalization Note.** A partial function is `(ι → Bool) → Option Bool`, with `none` for `∗`. -/
def Computes {ι : Type} (φ : Formula (DMLeaf ι)) (f : (ι → Bool) → Option Bool) : Prop :=
  ∀ x b, f x = some b → φ.eval dmVal x = b

/-- **Formula depth** `D(f)` (§3.1, p.7): "we write D(f) and L(f) for the minimum depth and the minimum
number of leaves of such a formula".

**Formalization Note.** `sInf` on `ℕ`; for a finite input set `ι` every partial function has a
formula (a DNF), so the set is nonempty and `D f` is an attained minimum (proved in the
verification file). A total `g` is `fun x => some (g x)`. -/
noncomputable def D {ι : Type} (f : (ι → Bool) → Option Bool) : ℕ :=
  sInf {d | ∃ φ : Formula (DMLeaf ι), Computes φ f ∧ φ.depth = d}

/-- **Formula size** `L(f)`: the minimum number of leaves of a De Morgan formula computing `f`
(§3.1, p.7). Same conventions as `D`. -/
noncomputable def L {ι : Type} (f : (ι → Bool) → Option Bool) : ℕ :=
  sInf {l | ∃ φ : Formula (DMLeaf ι), Computes φ f ∧ leafCount φ = l}

end OneOfManyCC.Supplement


