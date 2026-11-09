-- Prove2me | Definitions.Def_MinCostMaj_MCInst
-- name    : MinCostMaj_MCInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:30.041934+00:00
-- url     : https://prove2.me/theorems/d7bf6f01-3e3a-4c72-8ed4-91a95783d1fc
-- title:
--   Instances of $\mathrm{MinCostCSP}(\mathbf A)$, solutions, cost and $\mathrm{OPT}$
-- statement:
--   Fix a finite relational structure $\mathbf A=(A;R_1,\dots,R_p)$. An **instance** of $\mathrm{MinCostCSP}(\mathbf A)$ is a triple $(V,\mathcal C,\{c_x\}_{x\in V})$: a finite set $V$ of variables; a set $\mathcal C$ of constraints $(\mathbf x,R_i)$ with $\mathbf x\in V^{m}$ a tuple of variables of length $m=\mathrm{ar}(R_i)$ (variables may repeat); and for every variable a cost function $c_x:A\to\mathbb Q_{\ge0}\cup\{\infty\}$.
--
--   An assignment $\alpha:V\to A$ is a **solution** if $\alpha(\mathbf x)\in R_i$ for every constraint $(\mathbf x,R_i)$, with $\alpha$ applied componentwise. The **cost** of $\alpha$ is
--   $$\mathrm{cost}(\alpha)=\sum_{x\in V}c_x(\alpha(x))\in\mathbb Q_{\ge0}\cup\{\infty\},$$
--   and $\mathrm{OPT}$ is the minimum cost of a solution, or $\infty$ if there is none.
--
--   These are the objects whose approximability the main theorem classifies.
--
--   **Formalization Note** An instance is raw input data: the number $n$ of variables (named $0,\dots,n-1$), a list of constraints (relation index, scope list) and a list of cost rows with entries `some q` (cost $q$) or `none` (cost $\infty$). `WellFormed` singles out the lists that encode an instance of the definition (indices in range, scopes of the right length, $n$ rows of length $|A|$, nonnegative costs). Costs are read into $[0,\infty]$, and $\mathrm{OPT}$ is the infimum over the finitely many solutions.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Definition 2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MinCostMaj_Struct

namespace MinCostMaj

open scoped ENNReal

/-- **An instance of MinCostCSP(A)**, as finite input data (Definition 2.1).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Definition 2.1, p.5: "An instance … is a triple (V, C, {cx}x∈V),
where V is a set of variables; C is a set of constraints, and each constraint (x, R) ∈ C is a pair
with x ∈ V^m an m-tuple of variables from V, and R = Ri a relation of arity ar(R) = m for some
1 ≤ i ≤ p; and cx : A → Q≥0 ∪ {∞}."

* `n` — the variables are `0, …, n-1`;
* `cons` — the constraints, each a pair (index `i` of the relation `Rᵢ`, scope list of variables);
* `cost` — for every variable `x` a row of length `d`: entry `a` is `some q` for the finite cost
  `cₓ(a) = q` and `none` for `cₓ(a) = ∞`.

**Formalization Note.** Instances are raw lists so that algorithms (Turing machines) can read
them; `WellFormed` singles out the ones that encode a Definition 2.1 instance. Scopes may repeat
variables (`x ∈ V^m`). Relation indices are `0`-based. -/
structure MCInst where
  /-- number of variables -/
  n : ℕ
  /-- constraints: (relation index, scope) -/
  cons : List (ℕ × List ℕ)
  /-- cost rows, `none` = `∞` -/
  cost : List (List (Option ℚ))

/-- **Well-formed instance of MinCostCSP(A)**: every relation index is `< p`, every scope has the
arity of its relation and lists variables `< n`, there are `n` cost rows, each of length `d`, and
every finite cost is `≥ 0` (Definition 2.1, p.5: `cₓ : A → ℚ≥0 ∪ {∞}`). -/
def MCInst.WellFormed {d : ℕ} (A : Struct d) (I : MCInst) : Prop :=
  (∀ c ∈ I.cons, ∃ h : c.1 < A.p, c.2.length = A.ar ⟨c.1, h⟩ ∧ ∀ x ∈ c.2, x < I.n) ∧
  I.cost.length = I.n ∧
  (∀ row ∈ I.cost, row.length = d) ∧
  (∀ row ∈ I.cost, ∀ q : ℚ, some q ∈ row → 0 ≤ q)

/-- **Solution** (Definition 2.1, p.5): "An assignment α : V → A is a solution if α(x) ∈ R for
every (x, R) ∈ C, where α is applied componentwise."

**Formalization Note.** The side conditions `h`, `hl`, `hs` hold for every constraint of a
well-formed instance, so on well-formed instances this is exactly the source's condition. -/
def MCInst.IsSolution {d : ℕ} (A : Struct d) (I : MCInst) (α : Fin I.n → Fin d) : Prop :=
  ∀ c ∈ I.cons, ∀ (h : c.1 < A.p) (hl : c.2.length = A.ar ⟨c.1, h⟩)
    (hs : ∀ x ∈ c.2, x < I.n),
    (fun j : Fin (A.ar ⟨c.1, h⟩) =>
        α ⟨c.2.get (j.cast hl.symm), hs _ (List.get_mem _ _)⟩) ∈ A.rel ⟨c.1, h⟩

/-- The cost `cₓ(a) ∈ ℚ≥0 ∪ {∞}` read from the instance, as an element of `ℝ≥0∞` (`none ↦ ∞`). -/
noncomputable def MCInst.unaryCost {d : ℕ} (I : MCInst) (x : Fin I.n) (a : Fin d) : ℝ≥0∞ :=
  ((I.cost.getD x.val []).getD a.val none).elim ⊤ (fun q => ENNReal.ofReal (q : ℝ))

/-- **Cost of an assignment** (Definition 2.1, p.5): `cost(α) = Σ_{x∈V} cₓ(α(x))`, in
`ℚ≥0 ∪ {∞}` ⊆ `ℝ≥0∞`. -/
noncomputable def MCInst.costOf {d : ℕ} (I : MCInst) (α : Fin I.n → Fin d) : ℝ≥0∞ :=
  ∑ x : Fin I.n, I.unaryCost x (α x)

/-- **Optimum** `OPT(I)`: the minimum cost of a solution ("The goal is to find a solution of
minimum cost", Definition 2.1, p.5).

**Formalization Note.** The infimum is over the finitely many solutions, so it is attained when a
solution exists. It is `⊤` (= ∞) exactly when there is no solution or every solution uses an
infinite cost. -/
noncomputable def MCInst.OPT {d : ℕ} (A : Struct d) (I : MCInst) : ℝ≥0∞ :=
  ⨅ (α : Fin I.n → Fin d) (_ : I.IsSolution A α), I.costOf α

end MinCostMaj


