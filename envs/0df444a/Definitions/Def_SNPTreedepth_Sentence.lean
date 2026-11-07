-- Prove2me | Definitions.Def_SNPTreedepth_Sentence
-- name    : SNPTreedepth_Sentence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:00.427283+00:00
-- url     : https://prove2.me/theorems/fc5a3005-b10e-4bed-ba01-8f5e1e841993
-- title:
--   SNP sentences $\exists R_1\dots R_r\,\forall x_1\dots x_k\,\psi$, length $|\varphi|$, solutions and $Q$-solutions
-- statement:
--   An **SNP sentence** over the signature of $R=(V,E_1,\dots,E_b)$ is
--   $$
--   \varphi \;=\; \exists R_1,\dots,R_r\ \forall x_1,\dots,x_k:\ \psi(R_1,\dots,R_r,x_1,\dots,x_k),
--   $$
--   where $\psi$ is quantifier-free and built from the atoms $E_i(\bar u)$, $R_j(\bar u)$ and $x_n=x_{n'}$. The **length** $|\varphi|$ is the sum over all atom occurrences in $\psi$ of the number of element variables of the atom: $\mathrm{ar}(E_i)$, $\mathrm{ar}(R_j)$, or $2$ for an equality. The sentence is **well formed** when it obeys the paper's conventions: negations occur only in front of atoms, every $\mathrm{ar}(R_j)$ is positive, and every relation variable $R_j$, every element variable $x_n$ and every input relation $E_i$ occurs in $\psi$.
--
--   A **solution** is an instantiation $R'_1,\dots,R'_r$ of the relation variables under which $\psi(R'_1,\dots,R'_r,\bar v)$ holds for every $\bar v\in V^k$; $R\models\varphi$ means that a solution exists. For $Q\subseteq[r]$ a **$Q$-solution** is the restriction $(R'_j)_{j\in Q}$ of some solution.
--
--   **Formalization Note** The input signature of $\varphi$ is a type parameter, so a sentence is only ever evaluated on structures of the matching signature. The matrix is a formula in negation normal form; the other conventions form the predicate `WellFormed`. The paper states these as assumptions without loss of generality; they are what makes $|\varphi|$ bound the length of the code of $\varphi$.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), §3 SNP, pp.15–16 (PDF pp.16–17), Definition 16, p.16

import Mathlib
import Definitions.Def_SNPTreedepth_Structure

set_option autoImplicit false

namespace SNPTreedepth

/-- An **atom** of the matrix `ψ` of an SNP sentence (Depian et al., *A Uniform Algorithm for Strict
NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.15):
`E_i(ū)` for an input relation `i ∈ [b]`, `R_j(ū)` for a relation variable `j ∈ [r]`, or
`x_n = x_{n'}`, where `ū` is a tuple of element variables among `x₁, …, x_k`.

**Formalization Note** Element variables are `Fin k`, input relations `Fin σ.b`, relation variables
`Fin r` with arities `arR`. -/
inductive Atom (σ : Signature) (r : ℕ) (arR : Fin r → ℕ) (k : ℕ) where
  /-- `E_i(x_{n₁}, …, x_{n_a})`, `a = ar(E_i)` -/
  | inp (i : Fin σ.b) (args : Fin (σ.ar i) → Fin k)
  /-- `R_j(x_{n₁}, …, x_{n_a})`, `a = ar(R_j)` -/
  | var (j : Fin r) (args : Fin (arR j) → Fin k)
  /-- `x_n = x_{n'}` -/
  | eq (n n' : Fin k)

/-- A quantifier-free formula **in negation normal form** over atoms of type `A`: literals (an atom
or a negated atom) combined with `∧` and `∨`. This is the paper's convention (p.15) "negations in
ψ occur only directly in front of atoms". -/
inductive NNF (A : Type) where
  | pos (a : A)
  | neg (a : A)
  | and (φ ψ : NNF A)
  | or (φ ψ : NNF A)

namespace NNF

variable {A : Type}

/-- The list of atom occurrences of a formula, from left to right. -/
def atoms : NNF A → List A
  | pos a => [a]
  | neg a => [a]
  | and φ ψ => φ.atoms ++ ψ.atoms
  | or φ ψ => φ.atoms ++ ψ.atoms

/-- Truth of a formula when each atom `a` has truth value `val a`. -/
def eval (val : A → Prop) : NNF A → Prop
  | pos a => val a
  | neg a => ¬ val a
  | and φ ψ => φ.eval val ∧ ψ.eval val
  | or φ ψ => φ.eval val ∨ ψ.eval val

end NNF

/-- An **SNP sentence** `φ = ∃R₁, …, R_r ∀x₁, …, x_k : ψ(R₁, …, R_r, x₁, …, x_k)` on structures of
signature `σ` (Depian et al., p.15): `ψ` is a quantifier-free formula over the relations
`R₁, …, R_r, E₁, …, E_b` and the elements `x₁, …, x_k`, built from the atoms `E_i(ū)`, `R_j(ū)` and
`x_n = x_{n'}`.

**Formalization Note** The input signature of `φ` is the type parameter `σ`, so a sentence and a
structure can only be combined when their signatures match (p.15: "we always assume that the
signatures of R and φ match"). The matrix is stored in negation normal form (`NNF`); the paper's
remaining conventions are the predicate `Sentence.WellFormed`. -/
structure Sentence (σ : Signature) where
  /-- the number `r` of relation variables -/
  r : ℕ
  /-- the arity `ar(R_j)` of each relation variable -/
  arR : Fin r → ℕ
  /-- the number `k` of element variables -/
  k : ℕ
  /-- the quantifier-free matrix `ψ` -/
  ψ : NNF (Atom σ r arR k)

namespace Sentence

variable {σ : Signature}

/-- The number of (not necessarily distinct) element variables of an atom: `ar(E_i)`, `ar(R_j)`,
or `2` for an equality (Depian et al., p.15). -/
def atomLength (φ : Sentence σ) : Atom σ φ.r φ.arR φ.k → ℕ
  | .inp i _ => σ.ar i
  | .var j _ => φ.arR j
  | .eq _ _ => 2

/-- The **length** `|φ|` of an SNP sentence (Depian et al., p.15): "the sum, over all occurrences
of an atom in the inner formula ψ, of the number of (not necessarily distinct) element variables
of that atom; that is, an occurrence of an atom `x_n = x_{n'}` contributes length 2, and
occurrences of atoms `E_i(ū)` and `R_j(ū)` contribute length `ar(E_i)` and `ar(R_j)`,
respectively." -/
def length (φ : Sentence σ) : ℕ :=
  (φ.ψ.atoms.map φ.atomLength).sum

/-- The **arity** `ar(φ) = max_{i ∈ [r]} ar(R_i)` of an SNP sentence (Depian et al., p.15), with
`max ∅ = 0` (p.13). -/
def arity (φ : Sentence σ) : ℕ :=
  Finset.univ.sup φ.arR

/-- The element variables occurring in an atom. -/
def atomVars (φ : Sentence σ) : Atom σ φ.r φ.arR φ.k → Set (Fin φ.k)
  | .inp _ args => Set.range args
  | .var _ args => Set.range args
  | .eq n n' => {n, n'}

/-- The **conventions** that make `φ` an SNP sentence of the problem SNP Model Checking
(Depian et al., pp.15–16):
1. every relation variable has positive arity ("assume without loss of generality that each
   `ar(R_i)` is positive", p.15);
2. every relation variable `R_j` is mentioned in `ψ` (p.15);
3. every element variable `x_n` is mentioned in `ψ` (p.15);
4. every input relation `E_i` appears in `ψ` (p.16: "We also assume that R does not use any
   relations that do not appear in the formula").
Negation normal form (p.15) is built into the syntax `NNF`.

**Formalization Note** The paper states these as assumptions made without loss of generality; they
are what makes `|φ|` bound the size of the encoding of `φ` (p.15, `O(|φ| log |φ|)`) and the number
of sentences of a given length, so they are part of the definition here. -/
def WellFormed (φ : Sentence σ) : Prop :=
  (∀ j, 0 < φ.arR j) ∧
  (∀ j : Fin φ.r, ∃ args, Atom.var j args ∈ φ.ψ.atoms) ∧
  (∀ n : Fin φ.k, ∃ a ∈ φ.ψ.atoms, n ∈ φ.atomVars a) ∧
  (∀ i : Fin σ.b, ∃ args, Atom.inp i args ∈ φ.ψ.atoms)

/-- The value of an atom in the expansion `(R, R'₁, …, R'_r)` under the assignment `x`
(Depian et al., p.15). -/
def atomHolds {V : Type*} (φ : Sentence σ) (R : Structure σ V)
    (S : (j : Fin φ.r) → Set (Fin (φ.arR j) → V)) (x : Fin φ.k → V) :
    Atom σ φ.r φ.arR φ.k → Prop
  | .inp i args => (x ∘ args) ∈ R.rel i
  | .var j args => (x ∘ args) ∈ S j
  | .eq n n' => x n = x n'

/-- `R ⊨ ψ(R'₁, …, R'_r, v̄)` (Depian et al., p.15): `ψ` holds in the expansion
`(R, R'₁, …, R'_r)` when `R_j` is interpreted as `R'_j` and `x_n` is assigned `v_n`. -/
def Holds {V : Type*} (φ : Sentence σ) (R : Structure σ V)
    (S : (j : Fin φ.r) → Set (Fin (φ.arR j) → V)) (x : Fin φ.k → V) : Prop :=
  φ.ψ.eval (φ.atomHolds R S x)

/-- A **solution** (Depian et al., Definition 16, p.16): an instantiation `R'₁, …, R'_r` of the
relation variables, each `R'_j` a relation of arity `ar(R_j)` over `V`, under which `R ⊨ φ`, that
is, `ψ(R'₁, …, R'_r, v̄)` holds for every `v̄ ∈ V^k`. -/
def IsSolution {V : Type*} (φ : Sentence σ) (R : Structure σ V)
    (S : (j : Fin φ.r) → Set (Fin (φ.arR j) → V)) : Prop :=
  ∀ x : Fin φ.k → V, φ.Holds R S x

/-- `R ⊨ φ`: the SNP sentence `φ = ∃R₁, …, R_r ∀x₁, …, x_k : ψ` holds in `R` (Depian et al., p.15),
that is, `R` has a solution. -/
def Models {V : Type*} (φ : Sentence σ) (R : Structure σ V) : Prop :=
  ∃ S, φ.IsSolution R S

/-- A **Q-solution** (Depian et al., Definition 16, p.16): for `Q ⊆ [r]`, an instantiation
`(R'_i)_{i ∈ Q}` that agrees on `Q` with some solution; "equivalently, a Q-solution is the
projection to `(R_i)_{i ∈ Q}` of a solution".

**Formalization Note** The instantiation is given as a family over all of `[r]`; only its
components with index in `Q` matter. -/
def IsQSolution {V : Type*} (φ : Sentence σ) (R : Structure σ V) (Q : Finset (Fin φ.r))
    (S : (j : Fin φ.r) → Set (Fin (φ.arR j) → V)) : Prop :=
  ∃ S' : (j : Fin φ.r) → Set (Fin (φ.arR j) → V), φ.IsSolution R S' ∧ ∀ j ∈ Q, S' j = S j

end Sentence

end SNPTreedepth


