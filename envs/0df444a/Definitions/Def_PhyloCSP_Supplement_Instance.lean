-- Prove2me | Definitions.Def_PhyloCSP_Supplement_Instance
-- name    : PhyloCSP_Supplement_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:22:08.082371+00:00
-- url     : https://prove2.me/theorems/d5911170-1857-46d6-8865-659ea843fa33
-- title:
--   Instances of a phylogenetic CSP: constraints, satisfaction, value, complete satisfiability
-- statement:
--   Let $\Pi=(\varphi_i)_{i\in\iota}$ be a constraint language, $\varphi_i$ of arity $k_i$. An **instance** $I$ of $\mathrm{CSP}(\Pi)$ consists of variables $x_1,\dots,x_n$ and a finite collection (repetitions allowed) of **constraints** $\varphi_i(x_{j_1},\dots,x_{j_{k_i}})$ whose $k_i$ argument variables are **distinct**.
--
--   A **solution** is a rooted binary tree $T$ with leaf set $\{x_1,\dots,x_n\}$ (a pattern on the variables). It **satisfies** the constraint $\varphi_i(x_{j_1},\dots,x_{j_{k_i}})$ when the pattern of $x_{j_1},\dots,x_{j_{k_i}}$ in $T$, relabeled as $x_1,\dots,x_{k_i}$, belongs to $\mathrm{Sat}(\varphi_i)$. We write $\mathrm{sat}(I,T)$ for the number of satisfied constraints (with multiplicity), and the **value** of $T$ is
--   $$
--   \mathrm{val}(I,T)=\frac{\mathrm{sat}(I,T)}{\#\text{constraints of }I}.
--   $$
--   The instance is **completely satisfiable** if some solution satisfies all of its constraints. For a single predicate $\varphi$ we write $\mathrm{CSP}(\varphi)$ for $\mathrm{CSP}(\{\varphi\})$, the language with one predicate.
--
--   These notions are the objects of the tractability classification (Theorem 5.2), the trivial guarantee (Theorem 6.1) and the approximation results (Theorem 6.2).
--
--   **Formalization Note** Variables are `Fin n` (0-based); a constraint is a predicate index with an embedding `Fin (arity i) ↪ Fin n`; the constraints form a `List`. A solution is a pattern on exactly the variables, which loses nothing because restricting a solution to $\{x_1,\dots,x_n\}$ preserves which constraints hold (p.1). The value of an instance without constraints is $0/0=0$ in Lean; every statement using `value` restricts to instances with at least one constraint. `singleLang φ` is the one-predicate language.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.2 and the paragraph after it, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_PhyloCSP_ConstraintLanguage

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- **Instances of a phylogenetic CSP (Definition 1.2).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.2, p.1 (PDF p.3): "An instance I consists of
variables x1, . . . , xn and a collection of constraints of the form φ(xi1, . . . , xik), where
φ ∈ Π and all variables xi1, . . . , xik are distinct. A solution is a tree T whose leaf set contains
x1, . . . , xn. It satisfies a constraint φ(xi1, . . . , xik) if the formula holds in T. The value of
a solution is the fraction of constraints it satisfies. We say that an instance is completely
satisfiable if there is a solution satisfying all its constraints."

An instance of `CSP(L)` has `n` variables `x₁, …, xₙ` (the type `Fin n`, 0-based) and a list of
constraints; a constraint is a predicate index `i` of `L` together with an injective assignment of
the `arity i` arguments of `φᵢ` to variables.

**Formalization Note.** "A collection" allows repetitions, so the constraints form a `List`. The
arguments of a constraint are distinct variables, so they form an embedding
`Fin (arity i) ↪ Fin n`. -/
structure Instance (L : ConstraintLanguage) where
  /-- the number of variables -/
  n : ℕ
  /-- the constraints, with repetitions: a predicate index and its (distinct) argument variables -/
  constraints : List (Σ i : L.ι, Fin (L.arity i) ↪ Fin n)

/-- **The single-predicate language `{φ}`.** Definition 1.2, p.1 (PDF p.3): "For brevity, we write
CSP(φ) for CSP({φ})." The language with one predicate `φ` of arity `k`. -/
def singleLang {k : ℕ} (φ : Predicate k) : ConstraintLanguage where
  ι := Unit
  arity := fun _ => k
  sat := fun _ => φ

variable {L : ConstraintLanguage}

/-- A solution `T`, a tree on the variables, satisfies the constraint `⟨i, x⟩` when the pattern of
`x 0, …, x (k-1)` in `T` lies in `Sat(φᵢ)`.

**Formalization Note.** A solution is a pattern on exactly the variables `Fin n`: p.1 (PDF p.3),
"Every solution T can be replaced by the solution T↾{x1,...,xn}, whose leaf set is exactly
{x1, . . . , xn} and which satisfies exactly the same constraints." -/
def Satisfies (I : Instance L) (T : Pattern (Fin I.n))
    (c : Σ i : L.ι, Fin (L.arity i) ↪ Fin I.n) : Prop :=
  T.comap c.2 ∈ L.sat c.1

open Classical in
/-- The number of constraints of `I` (counted with multiplicity) that `T` satisfies. -/
noncomputable def satCount (I : Instance L) (T : Pattern (Fin I.n)) : ℕ :=
  I.constraints.countP (fun c => decide (Satisfies I T c))

/-- The value of a solution: the fraction of constraints it satisfies.

**Formalization Note.** For an instance without constraints the fraction is `0 / 0 = 0` in Lean;
every statement that uses `value` restricts to instances with at least one constraint. -/
noncomputable def value (I : Instance L) (T : Pattern (Fin I.n)) : ℝ :=
  (satCount I T : ℝ) / (I.constraints.length : ℝ)

/-- An instance is completely satisfiable if some solution satisfies all its constraints. -/
def CompletelySatisfiable (I : Instance L) : Prop :=
  ∃ T : Pattern (Fin I.n), ∀ c ∈ I.constraints, Satisfies I T c

end Supplement

end PhyloCSP


