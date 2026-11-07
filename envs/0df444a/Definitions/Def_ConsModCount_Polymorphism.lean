-- Prove2me | Definitions.Def_ConsModCount_Polymorphism
-- name    : ConsModCount_Polymorphism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:08.257752+00:00
-- url     : https://prove2.me/theorems/40680e5c-87e0-4ff2-802c-a949cd74ff56
-- title:
--   Polymorphisms, Mal'tsev, minority and conservative operations, term operations
-- statement:
--   A $k$-ary operation $f:D^k\to D$ **preserves** a relation $R\subseteq D^m$ if applying $f$ coordinatewise to any $k$ tuples of $R$ yields a tuple of $R$. A **polymorphism** of $H$ is an operation, of any arity $k$, preserving every relation of $H$.
--
--   A ternary operation $h$ is
--
--   1. **Mal'tsev** if $h(x,y,y)=h(y,y,x)=x$ for all $x,y$;
--   2. **minority** if $h(x,x,y)=h(x,y,x)=h(y,x,x)=y$ for all $x,y$;
--   3. **conservative** if $h(x,y,z)\in\{x,y,z\}$ for all $x,y,z$.
--
--   $H$ **has a Mal'tsev polymorphism** if some Mal'tsev operation is a polymorphism of $H$; conservativity of the operation is not required (for a conservative template it is automatic).
--
--   A **ternary term** in one operation symbol is a variable $x,y,z$ or an application of the symbol to three terms; its **term operation** in $(D;h)$ interprets variables as projections and the symbol as $h$.
--
--   These notions carry the tractability conditions of the classification.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §1, p.1 (PDF p.2): Mal'tsev, conservative operation, polymorphism; §2, (2), p.3 (PDF p.4): minority; p.3: terms in polymorphisms

import Mathlib
import Definitions.Def_ConsModCount_Template

set_option autoImplicit false

namespace ConsModCount

/-- A `k`-ary operation `f : D^k → D` **preserves** a relation `R ⊆ D^m`: applying `f`
coordinatewise to any `k` tuples of `R` gives a tuple of `R`. Xie, p.1 (PDF p.2): "A polymorphism
preserves each template relation under coordinatewise application." -/
def Preserves {D : Type} {k m : ℕ} (f : (Fin k → D) → D) (R : Set (Fin m → D)) : Prop :=
  ∀ t : Fin k → Fin m → D, (∀ l, t l ∈ R) → (fun j => f (fun l => t l j)) ∈ R

/-- A `k`-ary **polymorphism** of `H` (any arity `k`): an operation preserving every relation of
`H`. Xie, p.1 (PDF p.2). -/
def IsPolymorphism {D : Type} (H : Template D) {k : ℕ} (f : (Fin k → D) → D) : Prop :=
  ∀ i : Fin H.s, Preserves f (H.rel i)

/-- A ternary operation `h : D → D → D → D` viewed as an operation `D^3 → D`. -/
def ternary {D : Type} (h : D → D → D → D) : (Fin 3 → D) → D :=
  fun t => h (t 0) (t 1) (t 2)

/-- `h` is **Mal'tsev**: `h(x, y, y) = h(y, y, x) = x`. Xie, p.1 (PDF p.2). -/
def IsMaltsev {D : Type} (h : D → D → D → D) : Prop :=
  ∀ x y : D, h x y y = x ∧ h y y x = x

/-- `m` is a **minority** operation: `m(x, x, y) = m(x, y, x) = m(y, x, x) = y`. Xie, §2, (2),
p.3 (PDF p.4). -/
def IsMinority {D : Type} (m : D → D → D → D) : Prop :=
  ∀ x y : D, m x x y = y ∧ m x y x = y ∧ m y x x = y

/-- A ternary operation is **conservative** when its value is one of its arguments. Xie, p.1
(PDF p.2): "It is conservative if its value is one of its arguments." -/
def IsConservativeOp {D : Type} (h : D → D → D → D) : Prop :=
  ∀ x y z : D, h x y z = x ∨ h x y z = y ∨ h x y z = z

/-- `H` **has a Mal'tsev polymorphism**: some Mal'tsev operation `h` preserves every relation of
`H`. The operation is not required to be conservative (for a conservative template every
polymorphism is). -/
def HasMaltsev {D : Type} (H : Template D) : Prop :=
  ∃ h : D → D → D → D, IsMaltsev h ∧ IsPolymorphism H (ternary h)

/-- Ternary **terms** in one ternary operation symbol: the three variables and the application of
the symbol to three terms. -/
inductive Term3 : Type
  | var (i : Fin 3) : Term3
  | app (a b c : Term3) : Term3

/-- The **term operation** of `(D; h)` given by a term: variables are the projections, and an
application is the composition with `h`. -/
def Term3.eval {D : Type} (h : D → D → D → D) : Term3 → D → D → D → D
  | Term3.var i => fun x y z => ![x, y, z] i
  | Term3.app a b c => fun x y z => h (a.eval h x y z) (b.eval h x y z) (c.eval h x y z)

end ConsModCount


