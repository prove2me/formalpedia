-- Prove2me | Definitions.Def_AlgebraicPCSP_OneInThree_Structures
-- name    : AlgebraicPCSP_OneInThree_Structures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:38.321976+00:00
-- url     : https://prove2.me/theorems/790937c5-fd48-43eb-aba3-34198b423381
-- title:
--   1-in-3, not-all-equal, ternary structures (D; R) and cyclic operations (Example 2.8, Definition 8.2)
-- statement:
--   All structures here have a single ternary relation symbol.
--
--   1. For a set $D$ and a relation $R\subseteq D^3$, $(D;R)$ denotes the relational structure with domain $D$ and the one ternary relation $R$ (§8.1).
--   2. The **1-in-3 structure** is
--   $$\mathbf T=\big(\{0,1\};\ \{(1,0,0),(0,1,0),(0,0,1)\}\big),$$
--   the triples with exactly one entry equal to $1$ (Example 2.8).
--   3. The **not-all-equal structure** is
--   $$\mathbf H_2=\big(\{0,1\};\ \{0,1\}^3\setminus\{(0,0,0),(1,1,1)\}\big)$$
--   (Example 2.8).
--   4. An $n$-ary operation $s:D^n\to D$ is **cyclic** (Definition 8.2) if for all $(a_1,\dots,a_n)\in D^n$
--   $$s(a_1,a_2,\dots,a_n)=s(a_2,\dots,a_n,a_1).$$
--
--   $(\mathbf T,\mathbf H_2)$ is the PCSP template of 1-in-3 versus Not-All-Equal-SAT. Cyclic polymorphisms of prime arity are what the cited theorem of Barto and Kozik guarantees for every finite CSP template whose CSP is not NP-complete; §8 shows that no finite structure sandwiched between $\mathbf T$ and $\mathbf H_2$ has them.
--
--   **Formalization Note** The signature is the type `Unit` with arity $3$, and the structures are instances of the referenced `PCSPBLPAff.Symmetric.RelStruct`; homomorphisms and polymorphisms are the referenced `IsHom` and `IsPolymorphism`. The domain $\{0,1\}$ is `Fin 2`. Tuples are functions `Fin n → D`, and cyclicity is `s a = s (a ∘ finRotate n)`, where `(a ∘ finRotate n) i = a (i+1 mod n)`, i.e. the tuple $(a_2,\dots,a_n,a_1)$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 10, Example 2.8; p. 52, §8.1; p. 53, Definition 8.2

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- The signature of a single ternary relation symbol: the one symbol is `() : Unit`, and
its arity is `3`. -/
abbrev ternaryAr : Unit → ℕ := fun _ => 3

/-- A structure `(D; R)` with one ternary relation `R ⊆ D³` (§8.1, p. 52). -/
def ternaryStruct {D : Type} (R : Set (Fin 3 → D)) : RelStruct Unit ternaryAr D where
  rel _ := R

/-- The 1-in-3 structure `T = ({0, 1}; {(1, 0, 0), (0, 1, 0), (0, 0, 1)})`
(Example 2.8, p. 10). -/
def oneInThree : RelStruct Unit ternaryAr (Fin 2) :=
  ternaryStruct {x | x = ![1, 0, 0] ∨ x = ![0, 1, 0] ∨ x = ![0, 0, 1]}

/-- The not-all-equal structure `H₂ = ({0, 1}; {0, 1}³ ∖ {(0, 0, 0), (1, 1, 1)})`
(Example 2.8, p. 10). -/
def nae : RelStruct Unit ternaryAr (Fin 2) :=
  ternaryStruct {x | x ≠ ![0, 0, 0] ∧ x ≠ ![1, 1, 1]}

/-- An `n`-ary operation `s : Dⁿ → D` is cyclic (Definition 8.2, p. 53):
`s(a₁, a₂, …, aₙ) = s(a₂, …, aₙ, a₁)` for all `(a₁, …, aₙ) ∈ Dⁿ`. With `Fin n` indices,
`(a ∘ finRotate n) i = a (i + 1)` (indices mod `n`), so `a ∘ finRotate n` is the tuple
`(a₂, …, aₙ, a₁)`. -/
def IsCyclic {D : Type} {n : ℕ} (s : (Fin n → D) → D) : Prop :=
  ∀ a : Fin n → D, s a = s (a ∘ finRotate n)

end AlgebraicPCSP.OneInThree


