-- Prove2me | Definitions.Def_CH_SetTheoryLanguage
-- name    : CH_SetTheoryLanguage
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T22:22:46.022978+00:00
-- url     : https://prove2.me/theorems/6d3c3e12-5f4c-46a6-9768-00f9ff2bf1e3
-- title:
--   The first-order language of set theory and standard abbreviations
-- statement:
--   The first-order language of set theory $\mathcal L_\in=\{\in\}$: no function symbols, one binary relation symbol $\in$, and the equality of first-order logic. Formulas (type `SFormula`) are Mathlib's first-order formulas over $\mathcal L_\in$ whose free variables are named by natural numbers.
--
--   1. `mem x y` and `eq x y` are the atomic formulas $x\in y$ and $x=y$.
--   2. `all x φ` and `ex x φ` are $\forall x\,\varphi$ and $\exists x\,\varphi$, binding the named variable $x$.
--   3. `close φ` is the universal closure of $\varphi$, a sentence; a structure satisfies `close φ` iff $\varphi$ holds under every assignment of the variables.
--   4. Standard abbreviations: $x\subseteq y$, $x=\emptyset$, $s=z\cup\{z\}$, "$w$ is inductive", $w=\omega$ (the least inductive set), $p=\mathcal P(x)$, $\{a\}$, $\{a,b\}$, the Kuratowski pair $(a,b)=\{\{a\},\{a,b\}\}$, "$f$ is an injection / bijection from $x$ to $y$", $|x|\le|y|$ (`injects`), $|x|=|y|$ (`equinum`), and "$s$ is finite" (equinumerous with some $n\in\omega$).
--
--   This is the syntax layer on which ZF, ZFC, CH and GCH are stated as first-order theories and sentences.
--
--   **Formalization Note** Every abbreviation binds its own reserved variable names (all $\ge 1000$), and it is only ever applied to other variables, so no variable capture occurs.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; sections 'Cardinality of infinite sets' and 'Independence from ZFC' (the first-order setting of ZF/ZFC).

import Mathlib

/-!
# The first-order language of set theory

The language `setLang` has no function symbols and one binary relation symbol `∈`.
Formulas are Mathlib's first-order formulas over `setLang` whose free variables are
named by natural numbers (`SFormula = setLang.BoundedFormula ℕ 0 = setLang.Formula ℕ`).  The quantifiers `all x φ`
and `ex x φ` bind the named variable `x` in `φ`; `close φ` is the universal closure of
`φ`, a sentence.  The auxiliary formulas below (`subset`, `isPowerset`, `isOmega`,
`injects`, `equinum`, …) are the usual set-theoretic abbreviations; each one uses its own
reserved bound-variable names (all `≥ 1000`), which are never passed to it as arguments.
-/

namespace ContinuumHypothesis

open FirstOrder FirstOrder.Language

noncomputable section

/-- The relation symbols of set theory: a single binary symbol `∈`. -/
inductive SetRel : ℕ → Type
  | mem : SetRel 2

/-- The first-order language of set theory `{∈}` (with equality, built into first-order
logic). -/
@[reducible] def setLang : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := SetRel

/-- Formulas of set theory, with free variables named by natural numbers. -/
abbrev SFormula : Type := setLang.BoundedFormula ℕ 0

namespace SFormula

/-- The atomic formula `x ∈ y`. -/
def mem (x y : ℕ) : SFormula :=
  Relations.formula₂ (SetRel.mem : setLang.Relations 2) (Term.var x) (Term.var y)

/-- The atomic formula `x = y`. -/
def eq (x y : ℕ) : SFormula := Term.equal (Term.var x) (Term.var y)

/-- `∀ x, φ`: binds the named variable `x` in `φ`. -/
def all (x : ℕ) (φ : SFormula) : SFormula :=
  Formula.iAlls Unit (Formula.relabel (fun v => if v = x then Sum.inr () else Sum.inl v) φ)

/-- `∃ x, φ`: binds the named variable `x` in `φ`. -/
def ex (x : ℕ) (φ : SFormula) : SFormula :=
  Formula.iExs Unit (Formula.relabel (fun v => if v = x then Sum.inr () else Sum.inl v) φ)

/-- An upper bound for the names of the free variables of `φ`. -/
def varBound (φ : SFormula) : ℕ := φ.freeVarFinset.sup id

/-- The universal closure `∀ x₀ … x_N, φ` of `φ`, where `N = varBound φ`. -/
def close (φ : SFormula) : setLang.Sentence :=
  Formula.iAlls (Fin (varBound φ + 1))
    (Formula.relabel (fun n =>
      (Sum.inr ⟨n % (varBound φ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Empty ⊕ Fin _)) φ)

/-- `x ⊆ y`. -/
def subset (x y : ℕ) : SFormula := all 1000 (mem 1000 x ⟹ mem 1000 y)

/-- `x = ∅`. -/
def isEmpty (x : ℕ) : SFormula := all 1001 (∼(mem 1001 x))

/-- `s = z ∪ {z}` (the successor of `z`). -/
def isSucc (s z : ℕ) : SFormula := all 1002 (mem 1002 s ⇔ (mem 1002 z ⊔ eq 1002 z))

/-- `w` is inductive: `∅ ∈ w` and `w` is closed under `z ↦ z ∪ {z}`. -/
def isInductive (w : ℕ) : SFormula :=
  ex 1003 (isEmpty 1003 ⊓ mem 1003 w) ⊓
    all 1004 (mem 1004 w ⟹ ex 1005 (isSucc 1005 1004 ⊓ mem 1005 w))

/-- `w = ω`: `w` is the least inductive set. -/
def isOmega (w : ℕ) : SFormula :=
  isInductive w ⊓ all 1006 (isInductive 1006 ⟹ subset w 1006)

/-- `p = 𝒫(x)`. -/
def isPowerset (p x : ℕ) : SFormula := all 1007 (mem 1007 p ⇔ subset 1007 x)

/-- `t = {a}`. -/
def isSingleton (t a : ℕ) : SFormula := all 1008 (mem 1008 t ⇔ eq 1008 a)

/-- `t = {a, b}`. -/
def isDoubleton (t a b : ℕ) : SFormula := all 1009 (mem 1009 t ⇔ (eq 1009 a ⊔ eq 1009 b))

/-- `z = (a, b)`, the Kuratowski ordered pair `{{a}, {a, b}}`. -/
def isPair (z a b : ℕ) : SFormula :=
  all 1010 (mem 1010 z ⇔ (isSingleton 1010 a ⊔ isDoubleton 1010 a b))

/-- `(a, b) ∈ f`. -/
def pairIn (f a b : ℕ) : SFormula := ex 1011 (isPair 1011 a b ⊓ mem 1011 f)

/-- The relation `f` restricted to `x` is an injective function from `x` into `y`:
every `a ∈ x` is related by `f` to some `b ∈ y`, to at most one `b`, and distinct elements
of `x` are never related to the same `b`. -/
def isInjection (f x y : ℕ) : SFormula :=
  all 1012 (mem 1012 x ⟹ ex 1013 (mem 1013 y ⊓ pairIn f 1012 1013)) ⊓
  all 1012 (all 1013 (all 1014
    ((mem 1012 x ⊓ pairIn f 1012 1013 ⊓ pairIn f 1012 1014) ⟹ eq 1013 1014))) ⊓
  all 1012 (all 1015 (all 1013
    ((mem 1012 x ⊓ mem 1015 x ⊓ pairIn f 1012 1013 ⊓ pairIn f 1015 1013) ⟹ eq 1012 1015)))

/-- There is an injection from `x` into `y` (`|x| ≤ |y|`). -/
def injects (x y : ℕ) : SFormula := ex 1016 (isInjection 1016 x y)

/-- `f` restricted to `x` is a bijection from `x` onto `y`. -/
def isBijection (f x y : ℕ) : SFormula :=
  isInjection f x y ⊓ all 1017 (mem 1017 y ⟹ ex 1018 (mem 1018 x ⊓ pairIn f 1018 1017))

/-- `x` and `y` are equinumerous (`|x| = |y|`). -/
def equinum (x y : ℕ) : SFormula := ex 1019 (isBijection 1019 x y)

/-- `s` is finite: `s` is equinumerous with some natural number `n ∈ ω`. -/
def isFiniteSet (s : ℕ) : SFormula :=
  ex 1020 (isOmega 1020 ⊓ ex 1021 (mem 1021 1020 ⊓ equinum 1021 s))

end SFormula

end

end ContinuumHypothesis


