-- Prove2me | Definitions.Def_BudgetCoreExchange_QSAT2
-- name    : BudgetCoreExchange_QSAT2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.026627+00:00
-- url     : https://prove2.me/theorems/9a38b888-34fe-463a-a9be-48de2e2fe397
-- title:
--   QSAT$_2$: $\exists x\forall y\,\varphi(x,y)$ for DNF formulas
-- statement:
--   A formula $\varphi(x,y)$ in **disjunctive normal form** over the variables $x=(x_1,\dots,x_n)$ and $y=(y_1,\dots,y_m)$ is a list of terms $C_1,\dots,C_L$ (the paper calls them clauses); each term is a list of literals $x_i$, $\bar x_i$, $y_j$, $\bar y_j$ read as their conjunction, and $\varphi$ is the disjunction of its terms. The numbers $n$ and $m$ belong to the formula, so a variable need not occur.
--
--   **2-Quantified Satisfiability** is the language
--   $$
--   \mathrm{QSAT}_2=\{\langle\varphi\rangle : \exists x\in\{0,1\}^n\ \forall y\in\{0,1\}^m\ \ \varphi(x,y)\}.
--   $$
--   A formula is written over a seven-letter alphabet: $n$ and $m$ in unary, each followed by a separator, then every term as the codes of its literals (polarity, kind of variable, index in unary) followed by an end-of-term symbol.
--
--   QSAT$_2$ is the canonical $\Sigma_2^p$-complete problem from which the paper reduces.
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Appendix A, p.27 (definition of QSAT₂)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace BudgetCoreExchange

/-- A literal over the variables `x₁, …, xₙ` (`Sum.inl i`) and `y₁, …, yₘ` (`Sum.inr j`), with a
polarity (`true` for the variable, `false` for its negation). -/
abbrev Lit (n m : ℕ) : Type := (Fin n ⊕ Fin m) × Bool

/-- A Boolean formula `ϕ(x, y)` in **disjunctive normal form** over `n + m` variables
`x = (x₁, …, xₙ)`, `y = (y₁, …, yₘ)` (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A, p.27):
a list of terms `C₁, …, C_L` (called clauses in the paper), each a list of literals read as their
conjunction; the formula is the disjunction of its terms. The numbers `n` and `m` are part of the
formula (a variable need not occur). -/
structure DNF where
  n : ℕ
  m : ℕ
  terms : List (List (Lit n m))

namespace DNF

/-- The truth value of a literal under the assignment `(x, y)`. -/
def litTrue {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (ℓ : Lit n m) : Bool :=
  (match ℓ.1 with
    | Sum.inl i => x i
    | Sum.inr j => y j) == ℓ.2

/-- `ϕ(x, y)` holds: some term has all its literals true under `(x, y)`. -/
def Eval (ϕ : DNF) (x : Fin ϕ.n → Bool) (y : Fin ϕ.m → Bool) : Prop :=
  ∃ t ∈ ϕ.terms, ∀ ℓ ∈ t, litTrue x y ℓ = true

/-- `∃x∀y ϕ(x, y)` is true. -/
def QTrue (ϕ : DNF) : Prop :=
  ∃ x : Fin ϕ.n → Bool, ∀ y : Fin ϕ.m → Bool, ϕ.Eval x y

end DNF

/-- The alphabet in which DNF formulas are written: `one` (unary digit), `sep` (ends the unary
numbers `n` and `m`), `pos`/`neg` (polarity of a literal), `xv`/`yv` (kind of its variable),
`endTerm` (ends a term). -/
inductive QSym where
  | one
  | sep
  | pos
  | neg
  | xv
  | yv
  | endTerm
  deriving DecidableEq

instance : Fintype QSym where
  elems := {QSym.one, QSym.sep, QSym.pos, QSym.neg, QSym.xv, QSym.yv, QSym.endTerm}
  complete := by intro x; cases x <;> simp

namespace DNF

/-- Code of a literal: its polarity, the kind of its variable, then the variable's index in
unary. -/
def encodeLit {n m : ℕ} (ℓ : Lit n m) : List QSym :=
  (if ℓ.2 then QSym.pos else QSym.neg) ::
    (match ℓ.1 with
      | Sum.inl i => QSym.xv :: List.replicate i.val QSym.one
      | Sum.inr j => QSym.yv :: List.replicate j.val QSym.one)

/-- Code of a DNF formula: `n` and `m` in unary, each followed by `sep`, then every term as the
concatenation of its literals' codes followed by `endTerm`. -/
def encode (ϕ : DNF) : List QSym :=
  List.replicate ϕ.n QSym.one ++ QSym.sep :: List.replicate ϕ.m QSym.one ++ QSym.sep ::
    ϕ.terms.flatMap fun t => t.flatMap encodeLit ++ [QSym.endTerm]

end DNF

/-- **2-Quantified Satisfiability, QSAT₂** (Bichler–Waldherr, arXiv:1807.08253v1, Appendix A,
p.27): "Given a n + m variable Boolean formula ϕ(x,y) in DNF with x = (x1,...,xn) and
y = (y1,...,ym) is it true that ∃x∀yϕ(x,y)?" — the language of codes of DNF formulas `ϕ` for
which `∃x∀y ϕ(x, y)` is true. -/
def QSAT2 : CookPvsNP.Lang QSym :=
  { s | ∃ ϕ : DNF, ϕ.QTrue ∧ s = ϕ.encode }

end BudgetCoreExchange


