-- Prove2me | Definitions.Def_QCSepTotal_PartialFn
-- name    : QCSepTotal_PartialFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:28.983196+00:00
-- url     : https://prove2.me/theorems/8be6ec50-2168-4c68-95a6-52198db463a7
-- title:
--   Partial Boolean functions $F:X\times Y\to\{0,1,*\}$, their domain, and total functions
-- statement:
--   A **partial Boolean function** on inputs $X\times Y$ is a map $F : X\times Y\to\{0,1,*\}$; the symbol $*$ means undefined, and the **domain** is
--   $$\mathrm{dom}(F)=\{(x,y) : F(x,y)\neq *\}.$$
--   A **total function** $f : X\times Y\to\{0,1\}$ is a partial function with $\mathrm{dom}(f)=X\times Y$.
--
--   Theorem 1.4 converts a partial function on $\{0,1\}^n\times\{0,1\}^n$ into a total one.
--
--   **Formalization Note** The value $*$ is `none` and a bit $b$ is `some b`; bits are Booleans with `true` for $1$. Inputs are arbitrary types; the paper's $\{0,1\}^n$ is the type of Boolean $n$-tuples.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 1.4, p.2 (partial functions $\{0,1,*\}$, dom)

import Mathlib

namespace QCSepTotal

/-- A **partial Boolean function** `F : X × Y → {0, 1, ∗}` (F. Le Gall, *Improved Separations
between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726, held
version sha256 970e1476…, Theorem 1.4, p.2): `F x y = some b` is the value `b`, and `F x y = none`
is the symbol `∗` (undefined).

**Formalization Note.** The inputs are arbitrary types `X`, `Y`; the paper's `{0, 1}^n` is
`Fin n → Bool`. Bits are `Bool` (`true` = 1). -/
abbrev PartialFn (X Y : Type) : Type := X → Y → Option Bool

/-- The **domain** `dom(F)` of a partial function: the pairs where it is defined. -/
def PartialFn.dom {X Y : Type} (F : PartialFn X Y) : Set (X × Y) :=
  {p | (F p.1 p.2).isSome}

/-- A **total** function `f : X × Y → {0, 1}`, viewed as a partial function defined everywhere. -/
def total {X Y : Type} (f : X → Y → Bool) : PartialFn X Y :=
  fun x y => some (f x y)

end QCSepTotal


