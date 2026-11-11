-- Prove2me | Definitions.Def_OncePaid_Sparse_Parse
-- name    : OncePaid_Sparse_Parse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:46:07.187998+00:00
-- url     : https://prove2.me/theorems/d0bb1770-4f44-47e2-99d8-0c0f22866a88
-- title:
--   Affine forms and formal parses of a min-plus circuit: parse trees, their affine forms, occurrences and substitution
-- statement:
--   An **affine form** in the prices $c\in\mathbb R^\iota$ is $P(c)=\beta(P)+\sum_x\alpha_x(P)\,c_x$, with constant $\beta(P)\in\mathbb R$ and price coefficients $\alpha_x(P)$.
--
--   A **formal parse** of a gate $u$ of a min-plus circuit $C$ is a tree obtained by unfolding the DAG below $u$ and choosing one argument at every occurrence of a minimum gate. Every node is an **occurrence** of an original gate: a leaf is an occurrence of an input or constant gate; a unary node is an occurrence of a minimum gate together with a parse of the chosen argument, or of a scalar gate $\theta\cdot(\,)$ with a parse of its argument; a binary node is an occurrence of an addition gate with parses of both arguments. Different occurrences of one shared gate choose independently. A parse computes an affine form: an input $c_x$ gives $c_x$, a constant $r$ gives $r$, a scalar gate multiplies its child's form by $\theta$, and an addition adds the two forms.
--
--   Occurrences inside a parse are addressed by positions (the sequence of child choices from the root). Two positions are **disjoint** if neither is a prefix of the other. **Substitution** replaces the subparse at a position by another tree.
--
--   These notions are the language of Lemma 3.1 and of the descent and substitution arguments behind Theorem 3.4.
--
--   **Formalization Note** A parse is a plain tree `PTree` whose nodes record the index of the original gate; `Circuit.IsParse C t` checks that every node matches its gate (a minimum occurrence's child is rooted at one of the two arguments, a scalar or addition occurrence's children at its arguments). `parseForm` computes the affine form. Positions are lists of child indices `0`/`1`; `replaceAll` performs a list of substitutions in order.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 8, §2.2 and p. 12, §3.1 (PDF pp. 10, 14)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Circuit

namespace OncePaid.Sparse

/-!
# Affine forms and formal parses of a circuit

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), p. 8 §2.2 and p. 12 §3.1 (Lemma 3.1).

* An affine form `P(c) = β(P) + Σ_x α_x(P) c_x` is a constant `β` and a coefficient vector `α`.
* A formal parse is the tree obtained by unfolding the circuit DAG from a gate and choosing one
  argument at every occurrence of a minimum gate. It is encoded as a plain tree `PTree` whose
  nodes record the index of the original gate (`root`), together with the validity predicate
  `Circuit.IsParse`:
  - a `leaf u` is an occurrence of an input or constant gate `u`;
  - a `unary u t` is an occurrence of a minimum gate `u = min j k` whose chosen argument is the
    root of `t` (`j` or `k`), or of a scale gate `u = scale θ j` with child rooted at `j`;
  - a `binary u t₁ t₂` is an occurrence of an addition gate `u = add j k`, children rooted at
    `j` and `k`.
  Different occurrences of one shared gate choose independently.
* `Circuit.parseForm C t` is the affine form computed by the parse `t` (inputs give `c_x`,
  constants give `r`, scale gates multiply by `θ`, additions add).
* Occurrences are addressed by positions (lists of child indices `0`/`1`); `PTree.subtreeAt`,
  `PTree.replaceAt` and `PTree.replaceAll` read and substitute subparses at positions. Two
  positions are disjoint when neither is a prefix of the other.
-/

/-- An affine form `β + Σ_x α_x c_x` in the prices `c : ι → ℝ`. -/
structure AffineForm (ι : Type) where
  /-- the constant term `β(P)` (any sign) -/
  const : ℝ
  /-- the coefficient `α_x(P)` of the price `c_x` -/
  coef : ι → ℝ

namespace AffineForm

variable {ι : Type}

/-- Evaluation `P(c) = β(P) + Σ_x α_x(P) c_x`. -/
noncomputable def eval [Fintype ι] (P : AffineForm ι) (c : ι → ℝ) : ℝ :=
  P.const + ∑ x, P.coef x * c x

/-- Sum of affine forms. -/
instance : Add (AffineForm ι) := ⟨fun P Q => ⟨P.const + Q.const, P.coef + Q.coef⟩⟩

/-- Multiplication of an affine form by the real `θ`. -/
def smul (θ : ℝ) (P : AffineForm ι) : AffineForm ι := ⟨θ * P.const, θ • P.coef⟩

/-- All price coefficients are nonnegative. -/
def NonnegCoef (P : AffineForm ι) : Prop := ∀ x, 0 ≤ P.coef x

/-- The form `c_x`. -/
noncomputable def ofInput (x : ι) : AffineForm ι := by
  classical
  exact ⟨0, fun y => if y = x then 1 else 0⟩

/-- The constant form `r`. -/
def ofConst (r : ℝ) : AffineForm ι := ⟨r, 0⟩

end AffineForm

/-- A formal-parse tree; each node records the index of the original gate it is an occurrence
of. Validity with respect to a circuit is `Circuit.IsParse`. -/
inductive PTree where
  /-- an occurrence of an input or constant gate -/
  | leaf (u : ℕ)
  /-- an occurrence of a minimum gate (one chosen argument) or of a scale gate -/
  | unary (u : ℕ) (t : PTree)
  /-- an occurrence of an addition gate -/
  | binary (u : ℕ) (t₁ t₂ : PTree)

namespace PTree

/-- The original gate of the root occurrence. -/
def root : PTree → ℕ
  | leaf u => u
  | unary u _ => u
  | binary u _ _ => u

/-- The subparse at a position (list of child indices), if the position exists. -/
def subtreeAt : PTree → List ℕ → Option PTree
  | t, [] => some t
  | unary _ t, 0 :: o => subtreeAt t o
  | binary _ t₁ _, 0 :: o => subtreeAt t₁ o
  | binary _ _ t₂, 1 :: o => subtreeAt t₂ o
  | _, _ :: _ => none

/-- Replace the subparse at a position by `s` (no change if the position does not exist). -/
def replaceAt : PTree → List ℕ → PTree → PTree
  | _, [], s => s
  | unary u t, 0 :: o, s => unary u (replaceAt t o s)
  | binary u t₁ t₂, 0 :: o, s => binary u (replaceAt t₁ o s) t₂
  | binary u t₁ t₂, 1 :: o, s => binary u t₁ (replaceAt t₂ o s)
  | t, _ :: _, _ => t

/-- Replace the subparses at the listed positions, one after the other. -/
def replaceAll (t : PTree) (subs : List (List ℕ × PTree)) : PTree :=
  subs.foldl (fun acc p => replaceAt acc p.1 p.2) t

/-- The listed positions are pairwise disjoint occurrences: no position is a prefix of another
(in particular no position is listed twice). -/
def DisjointPositions (subs : List (List ℕ × PTree)) : Prop :=
  subs.Pairwise (fun a b => ¬ a.1 <+: b.1 ∧ ¬ b.1 <+: a.1)

end PTree

namespace Circuit

variable {ι : Type}

/-- `t` is a valid formal parse of gate `t.root` in the circuit `C`. -/
def IsParse (C : Circuit ι) : PTree → Prop
  | PTree.leaf u =>
      (∃ x, C.gates[u]? = some (Gate.input x)) ∨ (∃ r, C.gates[u]? = some (Gate.const r))
  | PTree.unary u t =>
      ((∃ j k, C.gates[u]? = some (Gate.min j k) ∧ (t.root = j ∨ t.root = k)) ∨
        (∃ θ j, C.gates[u]? = some (Gate.scale θ j) ∧ t.root = j)) ∧ IsParse C t
  | PTree.binary u t₁ t₂ =>
      (∃ j k, C.gates[u]? = some (Gate.add j k) ∧ t₁.root = j ∧ t₂.root = k) ∧
        IsParse C t₁ ∧ IsParse C t₂

/-- The affine form at a leaf gate. -/
noncomputable def leafForm : Option (Gate ι) → AffineForm ι
  | some (Gate.input x) => AffineForm.ofInput x
  | some (Gate.const r) => AffineForm.ofConst r
  | _ => ⟨0, 0⟩

/-- The scale applied at a unary occurrence (`θ` at a scale gate, `1` at a minimum gate). -/
def unaryScale : Option (Gate ι) → ℝ
  | some (Gate.scale θ _) => θ
  | _ => 1

/-- The affine form computed by a formal parse. -/
noncomputable def parseForm (C : Circuit ι) : PTree → AffineForm ι
  | PTree.leaf u => leafForm (C.gates[u]?)
  | PTree.unary u t => (parseForm C t).smul (unaryScale (C.gates[u]?))
  | PTree.binary _ t₁ t₂ => parseForm C t₁ + parseForm C t₂

end Circuit

end OncePaid.Sparse


