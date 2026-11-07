-- Prove2me | Definitions.Def_ConsModCount_Template
-- name    : ConsModCount_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:28.036646+00:00
-- url     : https://prove2.me/theorems/9499fda3-5604-4adf-9de4-291a42c9f0d3
-- title:
--   Finite relational templates, instances, solution counts and the partition function (1)
-- statement:
--   A **finite relational template** $H=(D;R_1,\dots,R_s)$ consists of a domain $D$ and finitely many relations $R_i\subseteq D^{k_i}$; the arity $k_i$ may be $0$ (a nullary relation, which is either true or false), and a relation may be empty.
--
--   $H$ is **conservative** if it contains every unary subset of $D$: for every $U\subseteq D$, including $\emptyset$ and $D$, some $R_i$ is unary and equals $U$.
--
--   An **instance** of $\mathrm{CSP}(H)$ has variables $V=\{0,\dots,n-1\}$ and a list of constraints $R_i(v_1,\dots,v_{k_i})$. Scopes may repeat variables, variables may occur in no constraint, and $n=0$ is allowed. An assignment $\sigma:V\to D$ satisfies the instance when $(\sigma(v_1),\dots,\sigma(v_{k_i}))\in R_i$ for every constraint. The **count** of the instance is the exact number of satisfying assignments; $\#_p\mathrm{CSP}(H)$ returns it modulo $p$.
--
--   With unary weights $w_v:D\to\mathbb F_p$ the **partition function** (1) is
--
--   $$Z=\sum_{\sigma:V\to D}\Big(\prod_{v\in V}w_v(\sigma(v))\Big)\Big(\prod_{C}[\sigma\text{ satisfies }C]\Big).$$
--
--   These objects are the input of every counting statement of the mission.
--
--   **Formalization Note** Finiteness and nonemptiness of $D$ are hypotheses of the theorems (`Fintype`, `Nonempty`), not fields of the structure.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §1, p.1 (PDF p.2): template, instance, #pCSP(H), conservative; Theorem 2, p.2 (PDF p.3), display (1)

import Mathlib

set_option autoImplicit false

namespace ConsModCount

/-- A **finite relational template** `H = (D; R₁, …, R_s)` on a domain `D`: `s` relations, the
`i`-th of arity `arity i` (arity `0`, a nullary relation, is allowed) given as a set of tuples
`Fin (arity i) → D`. Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission
(manuscript sha256 c673b4cc…), §1, p.1 (PDF p.2): "Let H = (D; R1, . . . , Rs) be a finite
relational template with nonempty domain."

**Formalization Note.** Finiteness and nonemptiness of `D` are not fields: every theorem that uses a
template assumes `[Fintype D] [DecidableEq D] [Nonempty D]`. A relation may be empty. -/
structure Template (D : Type) where
  /-- The number of relations. -/
  s : ℕ
  /-- The arity of each relation (`0` allowed). -/
  arity : Fin s → ℕ
  /-- The relations themselves. -/
  rel : (i : Fin s) → Set (Fin (arity i) → D)

/-- `H` is **conservative**: it contains every unary subset of `D`, i.e. for every `U ⊆ D`
(including `∅` and `D`) some relation of `H` is unary and equals `U`. Xie, p.1 (PDF p.2): "A
template is called conservative here if it contains every unary subset of D". -/
def Conservative {D : Type} (H : Template D) : Prop :=
  ∀ U : Set D, ∃ i : Fin H.s, H.arity i = 1 ∧
    ∀ t : Fin (H.arity i) → D, t ∈ H.rel i ↔ ∀ j, t j ∈ U

/-- An **instance** of `CSP(H)`: `n` variables `0, …, n-1` and a list of constraints
`R_i(v₁, …, v_k)`, each a relation index `i` with a scope `Fin (arity i) → Fin n`. Xie, p.1
(PDF p.2): "Constraint scopes may repeat variables; isolated variables and nullary relations are
allowed."

**Formalization Note.** The scope map need not be injective (repeated variables), variables that
occur in no constraint are allowed (isolated variables), and `n = 0` is allowed. -/
structure Instance {D : Type} (H : Template D) where
  /-- The number of variables. -/
  n : ℕ
  /-- The constraints, in order (repetitions allowed). -/
  constraints : List (Σ i : Fin H.s, Fin (H.arity i) → Fin n)

/-- An assignment `σ : V → D` satisfies the instance when every constraint `R_i(v₁, …, v_k)`
has `(σ v₁, …, σ v_k) ∈ R_i`. -/
def Instance.Sat {D : Type} {H : Template D} (I : Instance H) (σ : Fin I.n → D) : Prop :=
  ∀ c ∈ I.constraints, σ ∘ c.2 ∈ H.rel c.1

/-- The number of satisfying assignments `σ : V → D` of an instance (an exact natural number).
`#ₚCSP(H)` returns it modulo `p` (Xie, p.1, PDF p.2). -/
noncomputable def Instance.count {D : Type} [Fintype D] {H : Template D} (I : Instance H) : ℕ :=
  Nat.card {σ : Fin I.n → D // I.Sat σ}

/-- The weighted partition function (1) of Xie, Theorem 2, p.2 (PDF p.3): with unary weights
`w v : D → 𝔽ₚ`,
`Z = Σ_{σ : V → D} (Π_{v ∈ V} w_v(σ v)) · (Π_{C} [σ satisfies C])`. -/
noncomputable def Instance.weightedZ {D : Type} [Fintype D] {H : Template D} (I : Instance H)
    (p : ℕ) (w : Fin I.n → D → ZMod p) : ZMod p := by
  classical
  exact ∑ σ : Fin I.n → D, (∏ v, w v (σ v)) * (if I.Sat σ then 1 else 0)

end ConsModCount


