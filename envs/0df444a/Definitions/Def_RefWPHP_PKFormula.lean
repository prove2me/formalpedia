-- Prove2me | Definitions.Def_RefWPHP_PKFormula
-- name    : RefWPHP_PKFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:30.967996+00:00
-- url     : https://prove2.me/theorems/406e9d62-2f12-4987-8dc6-05f347c1c2e9
-- title:
--   Formulas of the cedent calculus PK: negation normal form, De Morgan negation, depth, size, substitution
-- statement:
--   Over a type $V$ of propositional variables, the **formulas of PK** are built from the literals $p$, $\neg p$ by conjunctions $\bigwedge_i \varphi_i$ and disjunctions $\bigvee_i \varphi_i$ of arbitrary finite fan-in. The empty conjunction is the constant $\top$ and the empty disjunction is the constant $\bot$.
--
--   1. The **negation** $\neg\varphi$ is an abbreviation: negations are pushed to the atoms and the connectives are interchanged (the De Morgan dual).
--   2. The **depth** is $\mathrm{depth}(\ell) = 0$ for a literal $\ell$, and $\mathrm{depth}(\bigwedge_i \varphi_i) = \mathrm{depth}(\bigvee_i \varphi_i) = 1 + \max_i \mathrm{depth}(\varphi_i)$.
--   3. The **size** is the number of symbols: a literal counts $1$, and a gate counts $1$ plus the sizes of its arguments.
--   4. A **substitution** $\sigma : V \to \mathrm{Form}(W)$ sends $p$ to $\sigma(p)$ and $\neg p$ to $\neg\sigma(p)$, and acts on gates argumentwise.
--
--   These are the objects every line of a PK derivation is made of, and the substitution is the operation by which the reduction of this mission turns a refutation of $\mathrm{Ref}_s(\varphi)$ into a refutation of the pigeonhole principle.
--
--   **Formalization Note** Fan-in is given by a list. The maximum over the empty list is $0$, so $\top$ and $\bot$ have depth $1$. The paper measures size as the length of a binary string (p.15); the symbol count differs from it by at most a logarithmic factor in the number of variables. A truth-value function `eval` is included only to state soundness facts.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.14 (PDF p.16)

import Mathlib

namespace RefWPHP

/-- Formulas of the cedent calculus PK of N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.14:
formulas "formed from literals together with conjunctions and disjunctions of unbounded fan-in",
over a type `V` of propositional variables.

**Formalization Note.** `and []` is the constant ⊤ and `or []` is the constant ⊥; the paper uses
both as formulas in (3.2c) and (3.3a)–(3.3e). Fan-in is given by a list. -/
inductive PKFormula (V : Type) : Type
  | pos : V → PKFormula V
  | neg : V → PKFormula V
  | and : List (PKFormula V) → PKFormula V
  | or : List (PKFormula V) → PKFormula V

namespace PKFormula

variable {V W : Type}

/-- The constant ⊤, the empty conjunction. -/
def top : PKFormula V := and []

/-- The constant ⊥, the empty disjunction. -/
def bot : PKFormula V := or []

/-- The negation `¬φ` of p.14: "an abbreviation for the corresponding formula where negations are
pushed to the atoms, interchanging connectives where needed" (De Morgan dual). -/
def dual : PKFormula V → PKFormula V
  | pos v => neg v
  | neg v => pos v
  | and l => or (l.attach.map fun ⟨φ, _⟩ => dual φ)
  | or l => and (l.attach.map fun ⟨φ, _⟩ => dual φ)

/-- Depth, p.14: `depth(ℓ) = 0` for a literal and `depth(⋀φᵢ) = depth(⋁φᵢ) = 1 + maxᵢ depth(φᵢ)`.

**Formalization Note.** The maximum of the empty list is `0`, so `⊤ = and []` and `⊥ = or []`
have depth 1. -/
def depth : PKFormula V → ℕ
  | pos _ => 0
  | neg _ => 0
  | and l => (l.attach.map fun ⟨φ, _⟩ => depth φ).foldr max 0 + 1
  | or l => (l.attach.map fun ⟨φ, _⟩ => depth φ).foldr max 0 + 1

/-- Size of a formula: its number of symbols (a literal counts 1, a gate counts 1 plus the sizes
of its arguments).

**Formalization Note.** The paper measures size as the length of a binary string (p.15); the
symbol count differs from it by at most a logarithmic factor in the number of variables. -/
def size : PKFormula V → ℕ
  | pos _ => 1
  | neg _ => 1
  | and l => (l.attach.map fun ⟨φ, _⟩ => size φ).sum + 1
  | or l => (l.attach.map fun ⟨φ, _⟩ => size φ).sum + 1

/-- Applying a substitution `σ : V → PKFormula W` (p.17, p.20): a positive literal `v` becomes
`σ v`, and a negative literal `¬v` becomes `¬σ(v)`, the dual of `σ v`. -/
def subst (σ : V → PKFormula W) : PKFormula V → PKFormula W
  | pos v => σ v
  | neg v => dual (σ v)
  | and l => and (l.attach.map fun ⟨φ, _⟩ => subst σ φ)
  | or l => or (l.attach.map fun ⟨φ, _⟩ => subst σ φ)

/-- Truth value under an assignment `a : V → Bool` (used only to state soundness facts). -/
def eval (a : V → Bool) : PKFormula V → Bool
  | pos v => a v
  | neg v => !a v
  | and l => l.attach.all fun ⟨φ, _⟩ => eval a φ
  | or l => l.attach.any fun ⟨φ, _⟩ => eval a φ

end PKFormula

end RefWPHP


