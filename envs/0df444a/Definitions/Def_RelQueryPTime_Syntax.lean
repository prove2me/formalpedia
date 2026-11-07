-- Prove2me | Definitions.Def_RelQueryPTime_Syntax
-- name    : RelQueryPTime_Syntax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:06.918537+00:00
-- url     : https://prove2.me/theorems/d40637c3-e107-4cc1-825e-77f7e36d4593
-- title:
--   Relational calculus with $\le$ and the least fixpoint operator: syntax, semantics, $\Sigma_\alpha$ levels, monotonicity
-- statement:
--   This module fixes the query language of the paper.
--
--   1. A **relational scheme** $\sigma = \langle R_1,\dots,R_k\rangle$ is a finite list of relation symbols, $R_i$ of arity $a_i$ (arities $0$ allowed).
--   2. An **ordered database** of scheme $\sigma$ with $n$ elements has domain $D = \{0,\dots,n-1\}$ with its natural order $\le$ and a relation $R_i \subseteq D^{a_i}$ for each symbol. Every finite totally ordered database is uniquely isomorphic to one of these, so no instance is lost.
--   3. **Formulas** are built from atoms $R_i(\bar x)$, $x \le y$, $x = y$ and $S_j(\bar x)$ (a relation variable $S_j$ of arity $a$), with $\neg$, $\wedge$, $\vee$, $\exists x$, $\forall x$, and the **least fixpoint** $\mathrm{LFP}(\varphi)(\bar v)$: the fixpoint is taken in a relation variable $S$ of arity $a$ with head variables $\bar x = (x_1,\dots,x_a)$, and $\bar v$ is substituted into it.
--   4. **Satisfaction** $B \models \varphi$ is the usual Tarskian one; $\mathrm{LFP}(\varphi)(\bar v)$ holds iff the value of $\bar v$ belongs to every relation $S$ with $\varphi(S) \subseteq S$, i.e. to the intersection of the relations closed under the operator $S \mapsto \{\bar u \mid B \models \varphi(S)[\bar u]\}$. For a monotone operator this is its least fixpoint.
--   5. The first-order levels of the **Fixpoint Hierarchy**: $\Sigma_0 = \Pi_0$ are the quantifier-free formulas, $\Sigma_{\alpha+1} = \{(\exists \bar x)\psi \mid \psi \in \Pi_\alpha\}$ and $\Pi_\alpha = \{\neg\varphi \mid \varphi \in \Sigma_\alpha\}$.
--   6. $\varphi$ is **monotone** in $S$ if $S \subseteq S'$ implies $\varphi(S) \subseteq \varphi(S')$, on every database and every assignment; $S$ occurs **positively** if each occurrence is under an even number of negations.
--   7. A formula is **well formed** if each LFP node has distinct head variables and a body monotone in its relation variable.
--   8. An $r$-ary **query** assigns to every ordered database $B$ and every $r$-tuple $\bar c$ a truth value; the formula $\varphi$ with free variables among $x_0,\dots,x_{r-1}$ defines the query $\bar c \mapsto B \models \varphi(\bar c)$.
--   9. $\mathrm{lfpAtom}(\varphi,\nu)$ is $\mathrm{LFP}(\varphi)(\bar v)$ in the shape of the definition of $\Sigma_\omega$: relation variable $0$ of arity $a$, head variables $x_0,\dots,x_{a-1}$, and $v_m = x_{\nu(m)}$ (repetitions allowed).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Variables are natural numbers and assignments are partial (an atom with an unassigned variable is false), so the empty domain $n = 0$ has an assignment. The LFP clause is the infimum of prefixed points written out, so the semantics is total also on non-monotone bodies; the classes FP and $\Sigma_\omega$ require monotone bodies. $(\exists \bar x)$ in $\Sigma_{\alpha+1}$ is a block of existential quantifiers, possibly empty.
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, §1 p.148 (relational scheme, relational calculus), §1 p.147 (relational database), §2 p.148 (monotone, LFP, the Fixpoint Hierarchy Σα, Πα, Σβ), §2 p.149 (ordered databases), proof of Theorem 1 p.149 (domain {0,…,n−1}) (PDF pp.1–3)

import Mathlib

namespace RelQueryPTime

/-- A relational scheme `⟨R₁ … R_k⟩` (Immerman, STOC 1982, §1, p.148): a finite list of relation
symbols, `R_i` of arity `a_i`.

**Formalization Note** The symbols are indexed by `Fin k`; arities may be `0`. -/
structure Schema where
  /-- the number `k` of relation symbols -/
  k : ℕ
  /-- the arity `a_i` of `R_i` -/
  arity : Fin k → ℕ

/-- An ordered relational database `B = ⟨D, R₁ … R_k⟩` of scheme `σ` with `n` elements
(Immerman, STOC 1982, §1, p.147; ordered databases §2, p.149, and "we can think of D as the set
of integers from 0 to n-1", proof of Theorem 1, p.149).

**Formalization Note** The domain is `Fin n` and the total order `≤` of the paper is the natural
order of `Fin n`: every finite totally ordered database is uniquely isomorphic to one of these.
Relations are `Bool`-valued tables on `a_i`-tuples. `n = 0` is allowed. -/
structure Database (σ : Schema) (n : ℕ) where
  /-- the table of `R_i`: `rel i t = true` iff `t ∈ R_i` -/
  rel : (i : Fin σ.k) → (Fin (σ.arity i) → Fin n) → Bool

/-- Formulas of relational calculus with the order `≤` and the least fixpoint operator
(Immerman, STOC 1982, §1, p.148 for relational calculus; §2, p.148 for `LFP`; the order `≤`,
§2, p.149).

Individual variables are natural numbers. `rvar j a xs` is the relation variable number `j` of
arity `a` applied to the variables `xs`. `lfp j a hd body vs` is `LFP(φ)(v)`: the least fixpoint
of the operator `R ↦ {u | body(R)[hd := u]}` in the `a`-ary relation variable `j`, with head
variables `hd`, applied to the variables `vs`.

**Formalization Note** `∧`, `∨`, `∀`, `∃` are all primitive, as on p.148. Bodies of `lfp` may
have parameters (free variables other than the head) and nested `lfp`. -/
inductive Formula (σ : Schema) : Type
  /-- `R_i(xs)` -/
  | rel (i : Fin σ.k) (xs : Fin (σ.arity i) → ℕ)
  /-- `x ≤ y` -/
  | le (x y : ℕ)
  /-- `x = y` -/
  | eq (x y : ℕ)
  /-- the relation variable `j` of arity `a`, applied to `xs` -/
  | rvar (j a : ℕ) (xs : Fin a → ℕ)
  /-- `¬φ` -/
  | neg (φ : Formula σ)
  /-- `φ ∧ ψ` -/
  | and (φ ψ : Formula σ)
  /-- `φ ∨ ψ` -/
  | or (φ ψ : Formula σ)
  /-- `(∃x) φ` -/
  | ex (x : ℕ) (φ : Formula σ)
  /-- `(∀x) φ` -/
  | all (x : ℕ) (φ : Formula σ)
  /-- `LFP(body)(vs)`, the fixpoint taken in relation variable `j` of arity `a`, head `hd` -/
  | lfp (j a : ℕ) (hd : Fin a → ℕ) (body : Formula σ) (vs : Fin a → ℕ)

/-- An assignment of domain elements to individual variables.

**Formalization Note** It is partial (`none` = unassigned), so that the empty domain `n = 0` has
an assignment; an atom mentioning an unassigned variable is false. -/
abbrev Env (n : ℕ) := ℕ → Option (Fin n)

/-- An assignment of relations to relation variables: `Ξ j a` is the `a`-ary relation assigned to
relation variable `j`. -/
abbrev RelEnv (n : ℕ) := (j a : ℕ) → (Fin a → Fin n) → Prop

/-- Update an assignment at variable `x`. -/
def Env.set {n : ℕ} (ρ : Env n) (x : ℕ) (d : Fin n) : Env n :=
  fun y => if y = x then some d else ρ y

/-- Assign the tuple `t` to the head variables `hd` (the other variables keep their values). -/
noncomputable def Env.bind {n a : ℕ} (ρ : Env n) (hd : Fin a → ℕ) (t : Fin a → Fin n) : Env n :=
  fun y => if h : ∃ m, hd m = y then some (t h.choose) else ρ y

open Classical in
/-- Update a relation assignment: relation variable `j` of arity `a` becomes `S`. -/
noncomputable def RelEnv.set {n : ℕ} (Ξ : RelEnv n) (j a : ℕ) (S : (Fin a → Fin n) → Prop) :
    RelEnv n :=
  fun j' a' t => if h : j' = j ∧ a' = a then S (h.2 ▸ t) else Ξ j' a' t

/-- The variables `xs` take the values `t` under `ρ`. -/
def Matches {n a : ℕ} (ρ : Env n) (xs : Fin a → ℕ) (t : Fin a → Fin n) : Prop :=
  ∀ m, ρ (xs m) = some (t m)

/-- Satisfaction `B ⊨ φ` under the assignments `ρ`, `Ξ` (Immerman, STOC 1982, §1–2, p.148).
`≤` is the order of `Fin n`. `LFP(φ)(v)` holds iff the value of `v` lies in every relation `S`
closed under the operator (`φ(S) ⊆ S`), i.e. in the intersection of the prefixed points, which is
the least fixpoint when the operator is monotone.

**Formalization Note** The `lfp` clause is the `sInf` of prefixed points written out (as in
Mathlib's `OrderHom.lfp`), so that `eval` is total also on non-monotone bodies; the fragments
`FP`, `Σ_ω` used in this mission require monotone bodies. -/
noncomputable def Formula.eval {σ : Schema} {n : ℕ} (B : Database σ n) :
    Formula σ → Env n → RelEnv n → Prop
  | .rel i xs, ρ, _ => ∃ t, Matches ρ xs t ∧ B.rel i t = true
  | .le x y, ρ, _ => ∃ d e, ρ x = some d ∧ ρ y = some e ∧ d ≤ e
  | .eq x y, ρ, _ => ∃ d, ρ x = some d ∧ ρ y = some d
  | .rvar j a xs, ρ, Ξ => ∃ t, Matches ρ xs t ∧ Ξ j a t
  | .neg φ, ρ, Ξ => ¬ φ.eval B ρ Ξ
  | .and φ ψ, ρ, Ξ => φ.eval B ρ Ξ ∧ ψ.eval B ρ Ξ
  | .or φ ψ, ρ, Ξ => φ.eval B ρ Ξ ∨ ψ.eval B ρ Ξ
  | .ex x φ, ρ, Ξ => ∃ d, φ.eval B (ρ.set x d) Ξ
  | .all x φ, ρ, Ξ => ∀ d, φ.eval B (ρ.set x d) Ξ
  | .lfp j a hd body vs, ρ, Ξ => ∃ t, Matches ρ vs t ∧
      ∀ S : (Fin a → Fin n) → Prop,
        (∀ u, body.eval B (ρ.bind hd u) (Ξ.set j a S) → S u) → S t

/-- `φ` is quantifier free (and has no `LFP`). -/
def Formula.IsQF {σ : Schema} : Formula σ → Prop
  | .neg φ => φ.IsQF
  | .and φ ψ | .or φ ψ => φ.IsQF ∧ ψ.IsQF
  | .ex _ _ | .all _ _ | .lfp _ _ _ _ _ => False
  | _ => True

/-- `φ` is first order: it contains no `LFP` (relational calculus with `≤`, p.148). -/
def Formula.IsFO {σ : Schema} : Formula σ → Prop
  | .neg φ | .ex _ φ | .all _ φ => φ.IsFO
  | .and φ ψ | .or φ ψ => φ.IsFO ∧ ψ.IsFO
  | .lfp _ _ _ _ _ => False
  | _ => True

mutual
  /-- The first-order levels `Σ_α` of the Fixpoint Hierarchy (Immerman, STOC 1982, §2, p.148):
  `Σ₀ = Π₀` = quantifier-free formulas, `Σ_{α+1} = {(∃x)ψ | ψ ∈ Π_α}`, `Π_α = {¬φ | φ ∈ Σ_α}`.

  **Formalization Note** `(∃x)` is a block of existential quantifiers `∃x₁ … ∃x_m` (possibly
  empty), so the levels are cumulative. -/
  def IsSigma {σ : Schema} : ℕ → Formula σ → Prop
    | 0, φ => φ.IsQF
    | α + 1, φ => ∃ (xs : List ℕ) (ψ : Formula σ), φ = xs.foldr Formula.ex ψ ∧ IsPi α ψ
  /-- The levels `Π_α = {¬φ | φ ∈ Σ_α}` (`Π₀` = quantifier-free formulas), p.148. -/
  def IsPi {σ : Schema} : ℕ → Formula σ → Prop
    | 0, φ => φ.IsQF
    | α + 1, ψ => ∃ φ', ψ = Formula.neg φ' ∧ IsSigma (α + 1) φ'
end

/-- Polarity of the `a`-ary relation variable `j` in `φ`: `φ.Polar j a true` says that every
occurrence of the variable is positive (under an even number of negations), `Polar j a false`
that every occurrence is negative. Formulas containing `LFP` are excluded. -/
def Formula.Polar {σ : Schema} (j a : ℕ) : Bool → Formula σ → Prop
  | s, .rvar j' a' _ => j' = j ∧ a' = a → s = true
  | s, .neg φ => φ.Polar j a (!s)
  | s, .and φ ψ | s, .or φ ψ => φ.Polar j a s ∧ ψ.Polar j a s
  | s, .ex _ φ | s, .all _ φ => φ.Polar j a s
  | _, .lfp _ _ _ _ _ => False
  | _, _ => True

/-- `φ` is monotone in the `a`-ary relation variable `j` (Immerman, STOC 1982, §2, p.148:
"`R₁ ⊆ R₂` implies `φ(R₁) ⊆ φ(R₂)`"), on every database and every assignment. -/
def MonotoneIn {σ : Schema} (j a : ℕ) (φ : Formula σ) : Prop :=
  ∀ (n : ℕ) (B : Database σ n) (ρ : Env n) (Ξ : RelEnv n) (S S' : (Fin a → Fin n) → Prop),
    (∀ t, S t → S' t) → φ.eval B ρ (Ξ.set j a S) → φ.eval B ρ (Ξ.set j a S')

/-- Well-formedness of `LFP`: every `LFP` node has distinct head variables and a body monotone
in its relation variable (Immerman, STOC 1982, §2, p.148: `LFP` is applied to monotone
expressions). -/
def Formula.Wf {σ : Schema} : Formula σ → Prop
  | .neg φ | .ex _ φ | .all _ φ => φ.Wf
  | .and φ ψ | .or φ ψ => φ.Wf ∧ ψ.Wf
  | .lfp j a hd body _ => Function.Injective hd ∧ MonotoneIn j a body ∧ body.Wf
  | _ => True

/-- The free individual variables of `φ`. -/
def Formula.fv {σ : Schema} : Formula σ → Set ℕ
  | .rel _ xs => Set.range xs
  | .le x y | .eq x y => {x, y}
  | .rvar _ _ xs => Set.range xs
  | .neg φ => φ.fv
  | .and φ ψ | .or φ ψ => φ.fv ∪ ψ.fv
  | .ex x φ | .all x φ => φ.fv \ {x}
  | .lfp _ _ hd body vs => (body.fv \ Set.range hd) ∪ Set.range vs

/-- An `r`-ary query on ordered databases of scheme `σ`: for every `n`, every database on
`Fin n` and every `r`-tuple `c`, whether `c` is in the answer. -/
abbrev Query (σ : Schema) (r : ℕ) := ∀ n, Database σ n → (Fin r → Fin n) → Prop

/-- The assignment sending variable `i < r` to `c_i` (and leaving the others unassigned). -/
def envOf {n r : ℕ} (c : Fin r → Fin n) : Env n :=
  fun i => if h : i < r then some (c ⟨i, h⟩) else none

/-- The `r`-ary query defined by `φ` with free variables `0, …, r-1`: `c ↦ B ⊨ φ(c)`. Relation
variables left free are interpreted as empty. -/
noncomputable def Formula.query {σ : Schema} (r : ℕ) (φ : Formula σ) : Query σ r :=
  fun _ B c => φ.eval B (envOf c) (fun _ _ _ => False)

/-- `LFP(φ)(v)` in the shape of the definition of `Σ_ω` (Immerman, STOC 1982, §2, p.148): the
fixpoint is taken in relation variable `0` of arity `a`, the head variables are `0, …, a-1`, and
the query variables `ν m` are substituted into it (repetitions allowed). -/
def lfpAtom {σ : Schema} {a r : ℕ} (φ : Formula σ) (ν : Fin a → Fin r) : Formula σ :=
  .lfp 0 a (fun m => m.val) φ (fun m => (ν m).val)

end RelQueryPTime


