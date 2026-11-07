-- Prove2me | Definitions.Def_RobustBoolPCSP_Template
-- name    : RobustBoolPCSP_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:50.093755+00:00
-- url     : https://prove2.me/theorems/48391572-cc9d-4840-a2ce-1d8122ab5c92
-- title:
--   Finite promise templates, unweighted instances, $\mathrm{err}_{\mathrm{str}}$, $\mathrm{err}_{\mathrm{wk}}$ and $\alpha(I)$
-- statement:
--   A **finite promise template** $T$ has a strong domain $A$, a weak domain $B$ and finitely many **relation pairs** $(P_j,Q_j)$, $j\in\iota$, with $P_j\subseteq A^{r_j}$ and $Q_j\subseteq B^{r_j}$. Arity $r_j=0$ (a nullary relation, $\emptyset$ or $\{()\}$) and empty relations are allowed. A **Boolean template** is one with $A=B=\{0,1\}$.
--
--   An (unweighted) **instance** $I$ of $T$ has variables $V=\{0,\dots,n-1\}$ and a multiset of $m$ constraints; a constraint $C$ names a relation symbol $j$ and an ordered scope $(u_1,\dots,u_{r_j})\in V^{r_j}$, which may repeat variables. For $m>0$,
--
--   $$\mathrm{err}_{\mathrm{str}}(s;I)=\frac1m\sum_C\mathbf 1[s(\mathrm{scope}(C))\notin P_C],\qquad \mathrm{err}_{\mathrm{wk}}(b;I)=\frac1m\sum_C\mathbf 1[b(\mathrm{scope}(C))\notin Q_C],$$
--
--   for $s:V\to A$ and $b:V\to B$, and $\alpha(I)=\min_{s:V\to A}\mathrm{err}_{\mathrm{str}}(s;I)$. When $m=0$ both errors and $\alpha(I)$ are $0$.
--
--   The module also provides the one-pair template $\{(P,Q)\}$ and the two-pair template $\{(P_1,Q_1),(P_2,Q_2)\}$. These objects are the input of every robustness statement of the mission.
--
--   **Formalization Note** The pairs are indexed by an arbitrary type $\iota$; finiteness of $\iota$, and finiteness and nonemptiness of $A$ (for the minimum), are hypotheses of the statements that need them. Constraints are kept in a list; the errors do not depend on its order.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §3.1, pp.14–15 (templates, instances, error functions, the m = 0 convention)

import Mathlib

set_option autoImplicit false

namespace RobustBoolPCSP

/-- A **finite promise template** `T` with strong domain `A`, weak domain `B` and relation pairs
`(P_j, Q_j)`, `P_j ⊆ A^{r_j}`, `Q_j ⊆ B^{r_j}`, indexed by `j : ι`.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §3.1, p.14: "A finite promise template T consists of nonempty finite domains A, B and
finitely many relation pairs (Pj, Qj), Pj ⊆ A^{rj}, Qj ⊆ B^{rj}."

**Formalization Note.** Finiteness of the index type `ι` and finiteness and nonemptiness of `A`, `B`
are not fields: every statement that uses a template assumes `[Fintype ι]` (and `[Fintype A]`,
`[Nonempty A]`, … where needed). The paper indexes the pairs by `[m]`; any finite index type is
equivalent. Arity `0` (a nullary relation, `∅` or `{()}`) and empty relations are allowed (p.15).
A Boolean template is a `Template ι Bool Bool` (`false` = 0, `true` = 1). -/
structure Template (ι A B : Type) where
  /-- The arity `r_j` of the `j`-th relation pair. -/
  r : ι → ℕ
  /-- The strong relation `P_j ⊆ A^{r_j}`. -/
  P : (j : ι) → Set (Fin (r j) → A)
  /-- The weak relation `Q_j ⊆ B^{r_j}`. -/
  Q : (j : ι) → Set (Fin (r j) → B)

/-- An (ordinary, unweighted) **instance** of a template `T` (§3.1, p.15): variables `Fin n` and a
multiset of constraints, here a `List` (order is irrelevant for the errors), each a relation symbol
`j` and an ordered scope `Fin (r_j) → Fin n`, which may repeat variables.
"An instance consists of a finite variable set V and a multiset of constraints. A constraint specifies
a relation symbol j and an ordered scope (u1, . . . , u_{rj}) ∈ V^{rj}, which may contain repeated
variables." -/
structure Instance {ι A B : Type} (T : Template ι A B) where
  /-- The number of variables. -/
  n : ℕ
  /-- The constraints, with multiplicity. -/
  cons : List (Σ j : ι, Fin (T.r j) → Fin n)

/-- The fraction of entries of a list satisfying a predicate, with the convention that it is `0`
for the empty list (§3.1, p.15: "When m = 0, both error functions and α(I) are defined to be
zero"). -/
noncomputable def fracOf {α : Type} (L : List α) (bad : α → Prop) : ℝ := by
  classical
  exact if L = [] then 0 else ((L.filter (fun c => decide (bad c))).length : ℝ) / L.length

/-- Strong error `err_str(s; I) = (1/m) Σ_C 1[s(scope(C)) ∉ P_C]` of `s : V → A` (§3.1, p.15),
`0` when `m = 0`. -/
noncomputable def Instance.errStr {ι A B : Type} {T : Template ι A B} (I : Instance T)
    (s : Fin I.n → A) : ℝ :=
  fracOf I.cons (fun c => s ∘ c.2 ∉ T.P c.1)

/-- Weak error `err_wk(b; I) = (1/m) Σ_C 1[b(scope(C)) ∉ Q_C]` of `b : V → B` (§3.1, p.15),
`0` when `m = 0`. -/
noncomputable def Instance.errWk {ι A B : Type} {T : Template ι A B} (I : Instance T)
    (b : Fin I.n → B) : ℝ :=
  fracOf I.cons (fun c => b ∘ c.2 ∉ T.Q c.1)

/-- The optimal strong error `α(I) = min_{s : V → A} err_str(s; I)` (§3.1, p.15). The minimum is over
the finite nonempty set `Fin n → A` (`A` finite and nonempty), so no default value arises. -/
noncomputable def Instance.alpha {ι A B : Type} [Fintype A] [Nonempty A]
    {T : Template ι A B} (I : Instance T) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun s : Fin I.n → A => I.errStr s)

/-- The template `{(P, Q)}` with a single relation pair (index type `Unit`). -/
def Template.single {A B : Type} {k : ℕ} (P : Set (Fin k → A)) (Q : Set (Fin k → B)) :
    Template Unit A B where
  r := fun _ => k
  P := fun _ => P
  Q := fun _ => Q

/-- The template `{(P₁, Q₁), (P₂, Q₂)}` with two relation pairs (index `Unit ⊕ Unit`: `inl` is the
first pair, `inr` the second). -/
def Template.pair {A B : Type} {k l : ℕ} (P₁ : Set (Fin k → A)) (Q₁ : Set (Fin k → B))
    (P₂ : Set (Fin l → A)) (Q₂ : Set (Fin l → B)) : Template (Unit ⊕ Unit) A B where
  r := Sum.elim (fun _ => k) (fun _ => l)
  P := fun j => match j with
    | Sum.inl _ => P₁
    | Sum.inr _ => P₂
  Q := fun j => match j with
    | Sum.inl _ => Q₁
    | Sum.inr _ => Q₂

end RobustBoolPCSP


