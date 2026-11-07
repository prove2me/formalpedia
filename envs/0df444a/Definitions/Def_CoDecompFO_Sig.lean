-- Prove2me | Definitions.Def_CoDecompFO_Sig
-- name    : CoDecompFO_Sig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:19.443943+00:00
-- url     : https://prove2.me/theorems/0b998f5a-18cb-4c6d-af7f-0644879ca44f
-- title:
--   Finite relational signatures, their language, homomorphisms, and $G^\circ$
-- statement:
--   A **signature** $\sigma$ consists of finitely many relation symbols $R_0,\dots,R_{r-1}$ with arities $\mathrm{ar}(R_i)\in\mathbb N_0$; arity $0$ is allowed. A **$\sigma$-structure** is a set with a relation $R^A\subseteq A^{\mathrm{ar}(R)}$ for each symbol. A **homomorphism** is a map $f:A\to B$ such that $R^A(\vec x)$ implies $R^B(f(\vec x))$ for each symbol and tuple.
--
--   For a structure $G$, the structure $G^\circ$ has one more binary relation $\circ\subseteq G^2$ that holds exactly of the pairs $(x,x)$. The paper's first-order logic has no equality symbol, and $\circ$ is how it models equality.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** The first-order language is Mathlib's: no function symbols, and the $n$-ary relation symbols are the symbols of arity $n$. In the signature with $\circ$, the symbol $\circ$ has index $0$ and the symbol $R_i$ has index $i+1$.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), A.1, p.52; A.4, p.53; A.7, p.53

import Mathlib

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- A **finite relational signature** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and
FO Model Checking*, arXiv:2611.04658, held file sha256 d550d7af…, A.1, p.52): "A signature σ is a
set S of relation symbols and an arity function ar : S → N0". The symbols are `Fin r`; arity `0` is
allowed.

**Formalization Note** Theorem 1.16 fixes a finite signature, so `Fin r` loses nothing. -/
structure Sig where
  /-- The number of relation symbols. -/
  r : ℕ
  /-- The arity of each symbol. -/
  ar : Fin r → ℕ

/-- The Mathlib first-order language of `σ`: no function symbols, and the `n`-ary relation symbols
are the symbols of `σ` of arity `n`. -/
def Sig.lang (σ : Sig) : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := fun n => {i : Fin σ.r // σ.ar i = n}

/-- The symbol `i`, as a relation symbol of `σ.lang`. -/
def Sig.rel (σ : Sig) (i : Fin σ.r) : σ.lang.Relations (σ.ar i) := ⟨i, rfl⟩

/-- An interpretation of the symbols of `σ` on `A`: for each `R ∈ S` a relation over `A` of arity
`ar(R)` (A.1, p.52). -/
abbrev Sig.Rels (σ : Sig) (A : Type) : Type := (i : Fin σ.r) → Set (Fin (σ.ar i) → A)

/-- The Mathlib structure given by an interpretation. -/
@[reducible] def Sig.structureOf (σ : Sig) {A : Type} (R : σ.Rels A) : σ.lang.Structure A where
  funMap := fun f _ => nomatch (show Empty from f)
  RelMap := fun {_} i args => R i.1 (fun j => args (Fin.cast i.2 j))

/-- The relation `R^A(x⃗)` of a `σ`-structure `A`. -/
def Sig.holds (σ : Sig) {A : Type} [σ.lang.Structure A] (i : Fin σ.r)
    (args : Fin (σ.ar i) → A) : Prop :=
  FirstOrder.Language.Structure.RelMap (σ.rel i) args

/-- A **homomorphism** (A.4, p.53): "a function f : A → B so that for each relation R ∈ S and each
tuple x⃗ from A with compatible arity, we have R^A(x⃗) ⟹ R^B(f(x⃗))". -/
def IsHom (σ : Sig) {A B : Type} [σ.lang.Structure A] [σ.lang.Structure B] (f : A → B) : Prop :=
  ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → A), σ.holds i args → σ.holds i (f ∘ args)

/-- The signature `σ` with one more binary symbol `∘` (A.7, p.53).

**Formalization Note** The symbol `∘` has index `0` and the symbol `i` of `σ` has index `i.succ`,
so the arities reduce definitionally. -/
def sigmaEq (σ : Sig) : Sig := ⟨σ.r + 1, Fin.cons (α := fun _ => ℕ) 2 σ.ar⟩

/-- The point set of `G°` (A.7, p.53). -/
def Circ (_σ : Sig) (M : Type) : Type := M

/-- `G°` (A.7, p.53): "the structure obtained from G by adding a new relation ∘ ⊆ G² which is
reflexive on every point but relates no distinct points". -/
instance Circ.structure (σ : Sig) (M : Type) [σ.lang.Structure M] :
    (sigmaEq σ).lang.Structure (Circ σ M) :=
  (sigmaEq σ).structureOf (A := M)
    (Fin.cases (motive := fun i => Set (Fin ((sigmaEq σ).ar i) → M))
      (fun args : Fin 2 → M => args 0 = args 1)
      (fun i => fun args : Fin (σ.ar i) → M => σ.holds i args))

end CoDecompFO


