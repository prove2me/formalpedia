-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_CNF
-- name    : MultiplierAssoc206_Resolution_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:13.675134+00:00
-- url     : https://prove2.me/theorems/4da6f9f6-a1a5-4449-8681-a5464d55780a
-- title:
--   CNF formulas, resolution refutations, size and width, substitutions and restrictions
-- statement:
--   A **literal** over a set of Boolean variables is a variable $x$ or its negation $\neg x$; a **clause** is a finite *set* of literals, read as their disjunction, and a **CNF formula** $\Phi$ is a finite set of clauses, read as their conjunction. A clause containing complementary literals $x,\neg x$ is a **tautology**. The **width** of a clause is its number of literals, and the width $w(\Phi)$ of a CNF is the maximum width of its clauses; $N$ denotes the number of variables occurring in $\Phi$.
--
--   The **resolution rule** derives the resolvent $A\vee B$ from $A\vee x$ and $B\vee\neg x$. A **resolution derivation** from $\Phi$ is a sequence of clauses, each of which is a clause of $\Phi$ or the resolvent of two earlier clauses of the sequence; there is no weakening rule. Its **size** is the length of the sequence and its **width** the maximum width of its clauses. A **refutation** is a derivation ending with the empty clause $\bot$. We write
--   $$\mathrm{size}_{\mathrm{Res}}(\Phi)=\min\{|\pi| : \pi \text{ refutes } \Phi\},\qquad w(\Phi\vdash\bot)=\min\{w(\pi) : \pi \text{ refutes } \Phi\}.$$
--
--   A **substitution** $\sigma$ maps every variable to a constant or to a literal over a possibly different set of variables. $C\sigma$ is obtained by replacing every literal by its image and deleting the literals that became false; $\Phi\sigma$ applies $\sigma$ to every clause and omits the clauses that have become trivially true (a literal became true, or the image contains complementary literals). A **restriction** $\rho$ maps every variable to a constant or to itself, and $\Phi{\restriction_\rho}$ denotes $\Phi\rho$.
--
--   These are the objects of the size–width tradeoff, the substitution lemma and the reduction; every later definition is stated over them.
--
--   **Formalization Note** A literal is a pair $(x,b)$ asserting $x=b$. Minimum size and width are infima in $\mathbb N$, which are $0$ for a formula without refutation; every formula of the mission to which they are applied is unsatisfiable, and resolution is complete, so the minimum is attained. A restriction is a map to `Option Bool`, turned into a substitution that sends an unset variable to itself.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.4–5 (printed pp.3–4), §2 Preliminaries: CNF formulas, Resolution, Substitutions, Restrictions

import Mathlib

namespace MultiplierAssoc206.Resolution

open Classical

/-! # CNF formulas, resolution, substitutions and restrictions

Liew, *Associativity of Multiplication Is Hard for Resolution*, §2 (PDF pp. 4–5).
A literal `(x, b)` asserts that the variable `x` takes the value `b`; so `(x, true)` is the
positive literal `x` and `(x, false)` is `¬x`. Clauses are finite *sets* of literals and a CNF is
a finite set of clauses. -/

/-- A literal over the variable type `α`: `(x, true)` is `x`, `(x, false)` is `¬x`. -/
abbrev Literal (α : Type) := α × Bool

/-- A clause: a finite set of literals, read as their disjunction. -/
abbrev Clause (α : Type) := Finset (Literal α)

/-- A CNF formula: a finite set of clauses, read as their conjunction. -/
abbrev CNF (α : Type) := Finset (Clause α)

section Semantics

variable {α : Type}

/-- An assignment satisfies a literal `(x, b)` when it gives `x` the value `b`. -/
def LitSat (a : α → Bool) (l : Literal α) : Prop := a l.1 = l.2

/-- An assignment satisfies a clause when it satisfies one of its literals. -/
def ClauseSat (a : α → Bool) (C : Clause α) : Prop := ∃ l ∈ C, LitSat a l

/-- An assignment satisfies a CNF when it satisfies every clause. -/
def CNFSat (a : α → Bool) (Φ : CNF α) : Prop := ∀ C ∈ Φ, ClauseSat a C

/-- A CNF is unsatisfiable when no assignment satisfies it. -/
def Unsatisfiable (Φ : CNF α) : Prop := ∀ a : α → Bool, ¬ CNFSat a Φ

/-- A clause is a tautology when it contains a pair of complementary literals. -/
def IsTautology (C : Clause α) : Prop := ∃ x : α, (x, true) ∈ C ∧ (x, false) ∈ C

/-- The width of a clause: the number of its literals. -/
def clauseWidth (C : Clause α) : ℕ := C.card

/-- The width `w(Φ)` of a CNF: the maximum width of its clauses (`0` for the empty CNF). -/
def cnfWidth (Φ : CNF α) : ℕ := Φ.sup Finset.card

/-- The set of variables occurring in a CNF. -/
noncomputable def cnfVars (Φ : CNF α) : Finset α := Φ.biUnion fun C => C.image Prod.fst

/-- The number `N` of variables of a CNF. -/
noncomputable def numVars (Φ : CNF α) : ℕ := (cnfVars Φ).card

end Semantics

section Resolution

variable {α : Type}

/-- `R` is the resolvent of `C₁ = A ∨ x` and `C₂ = B ∨ ¬x` on the variable `x`:
`R = A ∨ B`, where `A = C₁ ∖ {x}` and `B = C₂ ∖ {¬x}`. -/
def IsResolvent (C₁ C₂ R : Clause α) : Prop :=
  ∃ x : α, (x, true) ∈ C₁ ∧ (x, false) ∈ C₂ ∧
    R = C₁.erase (x, true) ∪ C₂.erase (x, false)

/-- A resolution derivation from `Φ`: a sequence of clauses, each of which is either an initial
clause of `Φ` or the resolvent of two earlier clauses of the sequence. There is no weakening
rule. -/
def IsDerivation (Φ : CNF α) (π : List (Clause α)) : Prop :=
  ∀ k (hk : k < π.length),
    π[k] ∈ Φ ∨ ∃ i j, ∃ (hi : i < k) (hj : j < k),
      IsResolvent (π[i]'(lt_trans hi hk)) (π[j]'(lt_trans hj hk)) π[k]

/-- A resolution refutation of `Φ`: a derivation that ends with the empty clause `⊥`. -/
def IsRefutation (Φ : CNF α) (π : List (Clause α)) : Prop :=
  IsDerivation Φ π ∧ π.getLast? = some ∅

/-- The size of a derivation is the length of its sequence of clauses. -/
def derivSize (π : List (Clause α)) : ℕ := π.length

/-- The width of a derivation: the maximum width of its clauses. -/
def derivWidth (π : List (Clause α)) : ℕ := (π.map Finset.card).foldr max 0

/-- `size_Res(Φ)`: the minimum size of a resolution refutation of `Φ`
(`sInf` in `ℕ`, hence `0` when `Φ` has no refutation). -/
noncomputable def sizeRes (Φ : CNF α) : ℕ :=
  sInf {s : ℕ | ∃ π, IsRefutation Φ π ∧ π.length = s}

/-- `w(Φ ⊢ ⊥)`: the minimum width of a resolution refutation of `Φ`
(`sInf` in `ℕ`, hence `0` when `Φ` has no refutation). -/
noncomputable def refWidth (Φ : CNF α) : ℕ :=
  sInf {w : ℕ | ∃ π, IsRefutation Φ π ∧ derivWidth π = w}

end Resolution

section Substitution

variable {α β : Type}

/-- A substitution from variables `α` to `β`: each variable is mapped to a constant
(`Sum.inl b`) or to a literal over `β` (`Sum.inr l`). -/
abbrev Substitution (α β : Type) := α → Bool ⊕ Literal β

/-- The image of a literal under a substitution: a constant or a literal over `β`.
If `σ x = c` then the literal `(x, b)` becomes the constant `c = b`; if `σ x = (y, b')` then
`(x, b)` becomes `(y, b')` for `b = true` and its negation `(y, !b')` for `b = false`. -/
def Literal.subst (σ : Substitution α β) (l : Literal α) : Bool ⊕ Literal β :=
  match σ l.1 with
  | Sum.inl c => Sum.inl (decide (c = l.2))
  | Sum.inr m => Sum.inr (m.1, if l.2 then m.2 else !m.2)

/-- The literals of `Cσ`: the images that are literals (false constants are removed). -/
noncomputable def Clause.substLits (σ : Substitution α β) (C : Clause α) : Clause β :=
  C.biUnion fun l =>
    match l.subst σ with
    | Sum.inl _ => ∅
    | Sum.inr m => {m}

/-- A clause becomes trivially true under `σ` when one of its literals becomes the constant
true, or when its image contains complementary literals. -/
def Clause.TriviallyTrue (σ : Substitution α β) (C : Clause α) : Prop :=
  (∃ l ∈ C, l.subst σ = Sum.inl true) ∨ IsTautology (C.substLits σ)

/-- `Φσ`: apply `σ` to every clause, omitting the clauses that have become trivially true and
removing the literals that have become false. -/
noncomputable def CNF.subst (σ : Substitution α β) (Φ : CNF α) : CNF β :=
  (Φ.filter fun C => ¬ C.TriviallyTrue σ).image (Clause.substLits σ)

/-- A restriction: each variable is set to a constant (`some b`) or left unset (`none`). -/
abbrev Restriction (α : Type) := α → Option Bool

/-- A restriction as a substitution: every variable maps to a constant or to itself. -/
def Restriction.toSubst (ρ : Restriction α) : Substitution α α := fun x =>
  match ρ x with
  | some b => Sum.inl b
  | none => Sum.inr (x, true)

/-- `Φ↾ρ`: the result of applying the restriction `ρ` to the CNF `Φ`. -/
noncomputable def CNF.restrict (ρ : Restriction α) (Φ : CNF α) : CNF α :=
  Φ.subst ρ.toSubst

/-- An assignment `a` extends the restriction `ρ` when it agrees with `ρ` on every set
variable. -/
def Extends (a : α → Bool) (ρ : Restriction α) : Prop :=
  ∀ x b, ρ x = some b → a x = b

/-- Renaming the variables of a CNF along `f : α → β` (no constants, no negations). -/
noncomputable def CNF.rename (f : α → β) (Φ : CNF α) : CNF β :=
  Φ.image fun C => C.image fun l => (f l.1, l.2)

/-- The extension `Φ^ext = Φ ∧ ⋀_{f ∈ ι} Def(Z_f)` of a CNF `Φ` over `α` by extension variables
`Z_f` (`Sum.inr f`, `f ∈ ι`), given the defining CNFs `Def(Z_f)` (Lemma 5.5). -/
noncomputable def CNF.extend {ι : Type} [Fintype ι] (Φ : CNF α) (Def : ι → CNF (α ⊕ ι)) :
    CNF (α ⊕ ι) :=
  Φ.rename Sum.inl ∪ Finset.univ.biUnion Def

end Substitution

end MultiplierAssoc206.Resolution


