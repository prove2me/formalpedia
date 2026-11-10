-- Prove2me | Definitions.Def_UniformSubpower_Supplied_Algebra
-- name    : UniformSubpower_Supplied_Algebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:19:59.228224+00:00
-- url     : https://prove2.me/theorems/de1f0967-f047-43f9-abfb-a741de1afb82
-- title:
--   Indexed signatures, algebras by full tables, supplied Mal'tsev instances, the generated subalgebra of their product, and selected-coordinate queries
-- statement:
--   An **indexed signature** $\sigma = (r_0, \dots, r_{k-1})$ is a finite list of natural numbers, the arities of the operation symbols $0, \dots, k-1$; nullary symbols ($r_j = 0$) are allowed. An **algebra** in $\sigma$ on a carrier $A$ assigns to every symbol $j$ a total operation $f_j : A^{r_j} \to A$. **Terms** of the original signature over a variable set $V$ are built from variables and symbols, and are evaluated in an algebra in the usual way. A ternary term $t$ is a **Mal'tsev term** of an algebra when
--   $$t(x, y, y) = x \quad\text{and}\quad t(x, x, y) = y \qquad \text{for all } x, y,$$
--   and a family of algebras in one signature has a **common Mal'tsev term** when one term is Mal'tsev in each of them.
--
--   For algebras $A_i$ ($i \in \iota$) in one signature and a set $G \subseteq \prod_i A_i$, the **generated subalgebra** $\mathrm{Sg}(G)$ is the least subset of $\prod_i A_i$ that contains $G$ and is closed under the coordinatewise application of every basic operation; a nullary symbol contributes its constant tuple. $\mathrm{Sg}(G)$ is empty when $G = \emptyset$ and there is no nullary symbol, and the empty product has the single empty tuple.
--
--   A **full-table algebra** has carrier $\{0, \dots, s-1\}$ and lists, for every symbol $j$, its complete value table on all $s^{r_j}$ argument tuples. An **instance** of the supplied-operation model consists of a signature, a number $n \ge 0$ of coordinates, full-table coordinate algebras $A_0, \dots, A_{n-1}$ (whose carrier sizes $s_i$ may differ), the index $d$ of a designated basic symbol, and a finite list $G$ of generator tuples $g \in \prod_i A_i$. The instance is **valid** when every $s_i \ge 1$, $r_d = 3$, and in every coordinate the table $m = f_d$ satisfies $m(x, y, y) = x$ and $m(x, x, y) = y$. Nothing else is assumed: no bound on $n$, $s_i$, the arities or the signature, and no idempotence or nilpotence.
--
--   A **query** is a finite list of prescriptions $(i, a)$ of natural numbers. It is **positive** when a single tuple $b \in \mathrm{Sg}(G)$ agrees with every prescription, i.e. $i < n$ and $b_i = a$ for each $(i, a)$ in the query. So a query that prescribes every coordinate is a full membership target; a query with an out-of-range coordinate, an out-of-range value or two different values for one coordinate is negative; and the empty query is positive iff $\mathrm{Sg}(G) \neq \emptyset$.
--
--   **Formalization Note.** Carriers of full-table algebras are `Fin s`; coordinates and symbols are indexed from $0$; the designated symbol is a field `mal` and its arity is required to be $3$ by `Instance.Valid`, which casts the arguments along that equality.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 3, §1.1; p. 4, Theorem 1.1; pp. 11–12, §3

import Mathlib

namespace UniformSubpower.Supplied

/-!
Indexed signatures, algebras, terms, generated subalgebras of heterogeneous products, and the
supplied-operation instances of Theorem 1.1 (Gkantzounis, *Uniform Subpower Membership for Finite
Mal'tsev Algebras*, §1.1, p. 3; §3, pp. 11–12).
-/

/-- An indexed signature: the list `(r₀, …, r_{k-1})` of the arities of its operation symbols.
Nullary symbols (`rⱼ = 0`) are allowed. -/
abbrev Signature := List ℕ

/-- The operation symbols of a signature, indexed `0, …, k-1`. -/
abbrev Signature.Sym (σ : Signature) : Type := Fin σ.length

/-- The arity of a symbol. -/
abbrev Signature.ar (σ : Signature) (j : σ.Sym) : ℕ := σ.get j

/-- An algebra in the signature `σ` on the carrier `A`: one total operation
`(Fin rⱼ → A) → A` for every symbol `j`. -/
structure Alg (σ : Signature) (A : Type) where
  op : (j : σ.Sym) → (Fin (σ.ar j) → A) → A

/-- Terms of the original signature over the variable set `V`. -/
inductive Term (σ : Signature) (V : Type) : Type where
  | var : V → Term σ V
  | app : (j : σ.Sym) → (Fin (σ.ar j) → Term σ V) → Term σ V

/-- Evaluation of a term in an algebra under an assignment of the variables. -/
def Term.eval {σ : Signature} {V A : Type} (alg : Alg σ A) (env : V → A) : Term σ V → A
  | .var v => env v
  | .app j ts => alg.op j (fun k => (ts k).eval alg env)

/-- A ternary term `t` of the original signature is a Mal'tsev term of `alg` when
`t(x, y, y) = x` and `t(x, x, y) = y` for all `x, y`. -/
def IsMaltsevTerm {σ : Signature} {A : Type} (alg : Alg σ A) (t : Term σ (Fin 3)) : Prop :=
  ∀ x y : A, t.eval alg ![x, y, y] = x ∧ t.eval alg ![x, x, y] = y

/-- A family of algebras in one signature has a common Mal'tsev term. -/
def HasCommonMaltsevTerm {σ : Signature} {ι : Type} {A : ι → Type}
    (alg : ∀ i, Alg σ (A i)) : Prop :=
  ∃ t : Term σ (Fin 3), ∀ i, IsMaltsevTerm (alg i) t

/-- Membership in the subalgebra generated by `G` in the product `∏ᵢ A i`: the least set
containing `G` and closed under the coordinatewise application of every basic operation
(a nullary symbol contributes its constant tuple). -/
inductive InSg {σ : Signature} {ι : Type} {A : ι → Type} (alg : ∀ i, Alg σ (A i))
    (G : Set (∀ i, A i)) : (∀ i, A i) → Prop where
  | gen {g : ∀ i, A i} : g ∈ G → InSg alg G g
  | app (j : σ.Sym) (args : Fin (σ.ar j) → ∀ i, A i) :
      (∀ k, InSg alg G (args k)) → InSg alg G (fun i => (alg i).op j (fun k => args k i))

/-- `Sg(G)`, the subalgebra (subuniverse, possibly empty) of `∏ᵢ A i` generated by `G`. -/
def Sg {σ : Signature} {ι : Type} {A : ι → Type} (alg : ∀ i, Alg σ (A i))
    (G : Set (∀ i, A i)) : Set (∀ i, A i) :=
  {b | InSg alg G b}

/-- An algebra given by full tables: carrier `Fin size`, and for every symbol `j` its complete
value table `(Fin rⱼ → Fin size) → Fin size`. -/
structure TableAlg (σ : Signature) where
  size : ℕ
  table : (j : σ.Sym) → (Fin (σ.ar j) → Fin size) → Fin size

/-- The algebra of a full-table description. -/
def TableAlg.toAlg {σ : Signature} (T : TableAlg σ) : Alg σ (Fin T.size) := ⟨T.table⟩

/-- An instance of the supplied-operation model of Theorem 1.1: an indexed signature `sig`,
the number `n` of coordinates, the coordinate algebras `A₀, …, A_{n-1}` given by full tables
(their carriers `Fin sᵢ` may differ), a designated basic symbol `mal`, and a finite list of
generator tuples `g ∈ ∏ᵢ Aᵢ`. -/
structure Instance where
  sig : Signature
  n : ℕ
  coord : Fin n → TableAlg sig
  mal : sig.Sym
  gens : List ((i : Fin n) → Fin (coord i).size)

/-- Validity of an instance: every carrier is nonempty, the designated symbol is ternary, and in
every coordinate algebra its table `m` satisfies `m(x, y, y) = x` and `m(x, x, y) = y`. -/
def Instance.Valid (I : Instance) : Prop :=
  (∀ i, 1 ≤ (I.coord i).size) ∧
  ∃ h : I.sig.ar I.mal = 3, ∀ (i : Fin I.n) (x y : Fin (I.coord i).size),
    (I.coord i).table I.mal (fun k => ![x, y, y] (Fin.cast h k)) = x ∧
    (I.coord i).table I.mal (fun k => ![x, x, y] (Fin.cast h k)) = y

/-- The generated subalgebra `Sg(G) ⊆ ∏ᵢ Aᵢ` of an instance. -/
def Instance.Sg (I : Instance) : Set ((i : Fin I.n) → Fin (I.coord i).size) :=
  UniformSubpower.Supplied.Sg (fun i => (I.coord i).toAlg) {g | g ∈ I.gens}

/-- A query: a list of prescriptions `(i, a)`, "coordinate `i` takes the value `a`". -/
abbrev Query := List (ℕ × ℕ)

/-- A query is positive when one tuple `b ∈ Sg(G)` agrees with every prescription: for every
`(i, a)` in the query, `i < n` and `bᵢ = a`. Malformed (`i ≥ n` or `a ≥ sᵢ`) and conflicting
prescriptions therefore make a query negative; the empty query is positive iff `Sg(G) ≠ ∅`. -/
def Instance.Positive (I : Instance) (Q : Query) : Prop :=
  ∃ b ∈ I.Sg, ∀ p ∈ Q, ∃ h : p.1 < I.n, ((b ⟨p.1, h⟩ : Fin _) : ℕ) = p.2

end UniformSubpower.Supplied


