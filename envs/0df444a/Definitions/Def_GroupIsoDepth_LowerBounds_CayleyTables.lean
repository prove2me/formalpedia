-- Prove2me | Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables
-- name    : GroupIsoDepth_LowerBounds_CayleyTables
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:40:25.889146+00:00
-- url     : https://prove2.me/theorems/5bb3fc0a-bb0d-469f-b76a-b05172ea2b1b
-- title:
--   Cayley-table input model: bit-encoded tables, valid group tables, Latin squares, table isomorphism and the total Group Isomorphism language
-- statement:
--   Fix an order $n$ and put $\ell=\lceil\log_2 n\rceil$. A **multiplication table of order $n$** is an $n\times n$ array whose entry $(i,j)$, $i,j\in[n]$, is written with $\ell$ bits; it has $N=n^2\ell$ input bits, and every bit string of that length is a table. The entry $T(i,j)\in\mathbb N$ is the number the $\ell$ bits encode, possibly $\ge n$. An instance of Group Isomorphism is a pair $(T_0,T_1)$ of tables of order $n$: $2N$ input bits.
--
--   - $T$ is a **valid group table** ($T\in\mathrm{VALID}_n$, Lemma 4.2) if every entry lies in $[n]$ and $([n],T)$ is a group: associative, with a two-sided identity and two-sided inverses.
--   - $T$ is an **abelian exponent-4 table** if moreover the operation is commutative and $x^4=e$ for all $x$.
--   - $T$ is a **Latin square** (quasigroup table) if every entry lies in $[n]$ and every row and every column is a permutation of $[n]$.
--   - Tables $T,T'$ are **isomorphic** if a bijection $\sigma$ of $[n]$ satisfies $\sigma(T(a,b))=T'(\sigma a,\sigma b)$ for all $a,b$.
--   - A table **represents** a group $G$ if some bijection $e:[n]\to G$ satisfies $T(a,b)=e^{-1}(e(a)e(b))$.
--   - The **total Group Isomorphism language** $\mathrm{GpI}_n$ is the set of pairs $(T_0,T_1)$ such that $T_0$ and $T_1$ are valid group tables and $T_0\cong T_1$. $\mathrm{VALID}_n$ and the Latin squares are languages over the $N$ bits of one table; $(T,T)$ is the diagonal pair.
--
--   **Formalization Note** Labels $[n]$ are `Fin n`; $\ell$ is `Nat.clog 2 n`; bit $b$ of an entry has weight $2^b$. Isomorphism is written as: for all $a,b,c\in[n]$, $T(a,b)=c\iff T'(\sigma a,\sigma b)=\sigma c$, which on tables with entries in $[n]$ is the displayed condition.
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Lemma 4.2 (p. 24, PDF 25); §5 intro and Observation 5.1 (p. 35, PDF 36); Theorem 5.2 (p. 36, PDF 37)

import Mathlib

namespace GroupIsoDepth.LowerBounds

/-! Grochow, Kardeş, Levet, *Group Isomorphism: Depth-2½ Circuits and Lower Bounds*, STOC 2027
submission (manuscript sha256 cd6cacd4…), §4.1 Lemma 4.2 (printed p. 24, PDF 25), §5 and
Theorem 5.2 (pp. 35–36, PDF 36–37).

The Cayley-table input model. A multiplication table of order `n` has rows and columns indexed
by the labels `[n] = Fin n`; each entry is written with `ℓ = ⌈log₂ n⌉ = Nat.clog 2 n` bits, so one
table has `N = n²⌈log₂ n⌉` input bits, and an instance of Group Isomorphism (a pair of tables of
order `n`) has `2N` input bits. Every bit string is an admissible input: an entry may encode a
number `≥ n` (an out-of-range label), and such a table is not a valid table. Bit `b` of an entry
carries weight `2^b` (bit `0` is the least significant). -/

/-- The input variables of one table of order `n`: (row `i`, column `j`, bit `b` of entry `(i, j)`). -/
abbrev TableVar (n : ℕ) := Fin n × Fin n × Fin (Nat.clog 2 n)

/-- The input variables of a pair of tables of order `n`: (which table `t ∈ {0,1}`, row, column, bit). -/
abbrev PairVar (n : ℕ) := Fin 2 × TableVar n

/-- The natural number written in entry `(i, j)` of the table `x`: `Σ_b x(i,j,b)·2^b`. -/
def entry {n : ℕ} (x : TableVar n → Bool) (i j : Fin n) : ℕ :=
  ∑ b : Fin (Nat.clog 2 n), if x (i, j, b) then 2 ^ (b : ℕ) else 0

/-- The first table `T₀` of a pair. -/
def fst {n : ℕ} (x : PairVar n → Bool) : TableVar n → Bool := fun v => x (0, v)

/-- The second table `T₁` of a pair. -/
def snd {n : ℕ} (x : PairVar n → Bool) : TableVar n → Bool := fun v => x (1, v)

/-- The pair `(T, T)`. -/
def diagPair {n : ℕ} (x : TableVar n → Bool) : PairVar n → Bool := fun v => x v.2

/-- `T` is a valid Cayley table of a group on `[n]` (the language `VALID_n` of Lemma 4.2): every
entry lies in `[n]`, and the operation `a ∘ b := T a b` on `Fin n` is associative, has a two-sided
identity, and every element has a two-sided inverse. -/
def IsGroupTable {n : ℕ} (T : Fin n → Fin n → ℕ) : Prop :=
  ∃ h : ∀ a b, T a b < n,
    let op : Fin n → Fin n → Fin n := fun a b => ⟨T a b, h a b⟩
    (∀ a b c, op (op a b) c = op a (op b c)) ∧
    ∃ e : Fin n, (∀ a, op e a = a ∧ op a e = a) ∧ ∀ a, ∃ b, op a b = e ∧ op b a = e

/-- `T` is a valid Cayley table of an **abelian** group on `[n]` in which `x⁴ = 1` for every `x`
(an abelian group of exponent dividing 4). -/
def IsAbelianExp4Table {n : ℕ} (T : Fin n → Fin n → ℕ) : Prop :=
  ∃ h : ∀ a b, T a b < n,
    let op : Fin n → Fin n → Fin n := fun a b => ⟨T a b, h a b⟩
    (∀ a b c, op (op a b) c = op a (op b c)) ∧
    (∀ a b, op a b = op b a) ∧
    ∃ e : Fin n, (∀ a, op e a = a ∧ op a e = a) ∧ (∀ a, ∃ b, op a b = e ∧ op b a = e) ∧
      ∀ a, op (op (op a a) a) a = e

/-- `T` is a Latin square (the multiplication table of a quasigroup) on `[n]`: every entry lies in
`[n]`, and every row and every column is a permutation of `[n]`. -/
def IsLatinSquare {n : ℕ} (T : Fin n → Fin n → ℕ) : Prop :=
  ∃ h : ∀ a b, T a b < n,
    (∀ a, Function.Bijective (fun b => (⟨T a b, h a b⟩ : Fin n))) ∧
    (∀ b, Function.Bijective (fun a => (⟨T a b, h a b⟩ : Fin n)))

/-- The tables `T` and `T'` on `[n]` are isomorphic: some bijection `σ` of `[n]` satisfies
`σ(T(a, b)) = T'(σ a, σ b)` for all `a, b`. (Stated so that it needs no range proof: for every label
`c ∈ [n]`, `T(a, b) = c` iff `T'(σ a, σ b) = σ c`.) -/
def TableIso {n : ℕ} (T T' : Fin n → Fin n → ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ a b c : Fin n, T a b = c ↔ T' (σ a) (σ b) = σ c

/-- The labelled table `x` is a Cayley table of the group `G`: some bijection `e : [n] → G`
satisfies `T(a, b) = e⁻¹(e a · e b)` for all labels `a, b`. -/
def RepresentsGroup {n : ℕ} (x : TableVar n → Bool) (G : Type*) [Mul G] : Prop :=
  ∃ e : Fin n ≃ G, ∀ a b : Fin n, entry x a b = (e.symm (e a * e b) : ℕ)

/-- Validity of one table, as a language over its `N = n²⌈log₂ n⌉` input bits. -/
def ValidGroup (n : ℕ) (x : TableVar n → Bool) : Prop := IsGroupTable (entry x)

/-- Latin squares, as a language over the `N` input bits of one table. -/
def LatinSq (n : ℕ) (x : TableVar n → Bool) : Prop := IsLatinSquare (entry x)

/-- The **total** Group Isomorphism language at order `n`, over the `2N` input bits of a pair of
tables: both tables are valid group tables and they are isomorphic. -/
def GpI (n : ℕ) (x : PairVar n → Bool) : Prop :=
  IsGroupTable (entry (fst x)) ∧ IsGroupTable (entry (snd x)) ∧
    TableIso (entry (fst x)) (entry (snd x))

end GroupIsoDepth.LowerBounds


