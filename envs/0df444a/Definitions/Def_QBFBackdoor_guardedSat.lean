-- Prove2me | Definitions.Def_QBFBackdoor_guardedSat
-- name    : QBFBackdoor_guardedSat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:11.369649+00:00
-- url     : https://prove2.me/theorems/7a7abdb2-65aa-4619-b1e4-663d01171c7f
-- title:
--   Guarded conjunctions over $k$ disjuncts: semantics, restriction and length
-- statement:
--   Fix an arbitrary type of atoms $R$ with a semantics on assignments of $n$ variables and a length $|R|$. A **$k$-Disjunct** matrix is $\phi_1\vee\cdots\vee\phi_k$, each $\phi_i$ a conjunction of atoms. Its length is
--
--   $$
--   \lVert\Phi\rVert = n+\sum_{i=1}^{k}\Bigl(1+\sum_{R\in\phi_i}(1+|R|)\Bigr).
--   $$
--
--   Add $h$ fresh variables $Z=\{z_1,\dots,z_h\}$. A **guarded atom** $R\vee T$, with $T$ a clause on $Z$, holds when a literal of $T$ is true or $R$ holds of the original variables. For an assignment $\tau$ to $Z$, the **restriction after deleting true atoms** of a conjunction of guarded atoms deletes every atom with a literal of $T$ true under $\tau$ and keeps the original atom $R$ of every other one (all its guard literals are false). The length of a guarded conjunction on $n+h$ variables is $n+h+\sum(1+|R|+|T|)$.
--
--   For clausal atoms $R$, the guarded atom $R\vee T$ is itself a clause, $R\cup T$; this gives a CNF QBF with prefix $Q\,\exists Z$.
--
--   These notions state the reverse reduction of Lemma 4.4, from a disjunction of $k$ formulas of a class $\mathcal C$ to one formula with a strong backdoor of size $\lceil\log_2 k\rceil$ to $\mathcal C$.
--
--   **Formalization Note** The selector variables are the last $h$ of `Fin (n + h)`. The module defines `disjSat`, `guardedSat`, `residual`, `disjSize`, `guardedSize` and `guardedCNF`.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Lemma 4.4 and its proof, pp.20–21; §3.1, p.14 (guarded atoms, ∥Φ∥)

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_QSAT
import Definitions.Def_QBFBackdoor_PrefixHolds

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- **The matrix of a k-Disjunct-QBF(C) formula** for an arbitrary class of atoms. Eriksson,
Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean Formulas*,
arXiv:2604.15927 (held version, sha256 3ea1662e…), §3.2, p.16, and Lemma 4.4, p.20.

The atoms have an arbitrary type `α` with a semantics `sat : α → (Fin n → Bool) → Prop`; a
disjunct is a list of atoms read as a conjunction, and the matrix `ϕ₁ ∨ … ∨ ϕ_k` is true under `x`
when some disjunct has all its atoms satisfied. -/
def disjSat {α : Type} {n : ℕ} (sat : α → (Fin n → Bool) → Prop) (disj : List (List α))
    (x : Fin n → Bool) : Prop :=
  ∃ ϕ ∈ disj, ∀ R ∈ ϕ, sat R x

/-- **A guarded atom `R ∨ T`** over the original variables `Fin n` and `h` selector variables
`Z = {z₁, …, z_h}` (the last `h` of `Fin (n + h)`). §3.1, p.14: "a guarded atom R(x)∨T(z), stored
as the original atom and a clausal guard." The guard `T` is a set of literals on `Z`; the atom is
true under `x` when a guard literal is true or `R` holds of the original variables. -/
def guardedSat {α : Type} {n h : ℕ} (sat : α → (Fin n → Bool) → Prop)
    (a : α × Finset (Fin h × Bool)) (x : Fin (n + h) → Bool) : Prop :=
  (∃ l ∈ a.2, x (Fin.natAdd n l.1) = l.2) ∨ sat a.1 (fun v => x (Fin.castAdd h v))

/-- **Restriction of a guarded conjunction by an assignment `τ` to `Z`, after deleting true
atoms** (Lemma 4.4, proof, p.20: "restriction leaves exactly ϕi after deleting true atoms"). The
atoms with a guard literal true under `τ` become `⊤` and are deleted; every other atom has all its
guard literals false, so its guard vanishes and the original atom `R` remains. -/
def residual {α : Type} {h : ℕ} (τ : Fin h → Bool) (atoms : List (α × Finset (Fin h × Bool))) :
    List α :=
  (atoms.filter (fun a => !decide (∃ l ∈ a.2, τ l.1 = l.2))).map Prod.fst

/-- **The length `∥Φ∥` of a k-Disjunct formula** (§3.1, p.14: "the length of the explicit
representation, including the prefix, atom arguments, and relation descriptions"), given the
length `sz R` of each atom: one symbol per variable of the prefix, one per disjunct, and `1 + sz R`
per atom. -/
def disjSize {α : Type} (sz : α → ℕ) (n : ℕ) (disj : List (List α)) : ℕ :=
  n + (disj.map (fun ϕ => 1 + (ϕ.map (fun R => 1 + sz R)).sum)).sum

/-- **The length of a guarded conjunctive QBF** on `n + h` variables: one symbol per prefix
variable, and, per guarded atom `R ∨ T`, one symbol plus `sz R` plus one per guard literal. -/
def guardedSize {α : Type} {h : ℕ} (sz : α → ℕ) (n : ℕ) (atoms : List (α × Finset (Fin h × Bool))) :
    ℕ :=
  n + h + (atoms.map (fun a => 1 + sz a.1 + a.2.card)).sum

/-- **The CNF form of a guarded clausal conjunction** (Lemma 4.4, p.21: "If R is a clause, R∨Ti is
a clause too"). For clausal atoms `R` (sets of literals on `Fin n`) and guards on the `h` selector
variables, the clause `R ∪ T` on `Fin (n + h)`, with prefix `q` followed by the existential block
`Z`. -/
def guardedCNF {n h : ℕ} (q : Fin n → Bool)
    (atoms : List (Finset (Fin n × Bool) × Finset (Fin h × Bool))) : QBF (n + h) atoms.length where
  q := Fin.append q (fun _ => true)
  clause := fun j =>
    (atoms.get j).1.image (fun l => (Fin.castAdd h l.1, l.2)) ∪
      (atoms.get j).2.image (fun l => (Fin.natAdd n l.1, l.2))

end QBFBackdoor


