-- Prove2me | Definitions.Def_RefWPHP_Supplement_ResRefutation
-- name    : RefWPHP_Supplement_ResRefutation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:20:49.494866+00:00
-- url     : https://prove2.me/theorems/714a45c2-fcb2-44e9-923b-a92380c290b2
-- title:
--   Resolution refutations of a CNF with justifications: length and depth
-- statement:
--   A **Resolution refutation** of a CNF formula $\varphi = C_1 \wedge \dots \wedge C_m$ over $x_1, \dots, x_n$ is a sequence of clauses $D_1, \dots, D_s$ with $D_s = \bot$, the empty clause, such that every $D_i$ is
--
--   1. a clause $C_A$ of $\varphi$, or
--   2. a weakening $D_i \supseteq D_j$ of an earlier clause, $j < i$, or
--   3. the resolvent $A \vee B$ of earlier clauses $D_j = A \vee x$ and $D_k = B \vee \neg x$, $j, k < i$, or
--   4. a logical axiom $x \vee \neg x$.
--
--   Its **length** is $s$. The refutation determines a directed acyclic graph on its lines, with an edge from each line to the earlier lines it cites; its **depth** is the number of edges of the longest path from the last line $\bot$ to a line with no premises.
--
--   These are the objects of Definitions 4.2 and 4.3, whose hypotheses bound the length and the depth of Resolution refutations.
--
--   **Formalization Note** Each line stores its clause and its justification (`ax`, `lem`, `weak`, `res`), since depth depends on the dag and not only on the list of clauses. In rule 3, $A = D_j \setminus \{x\}$ and $B = D_k \setminus \{\neg x\}$, and the resolvent is exactly $A \cup B$. `DepthAtMost D` asserts a labelling of the lines that grows by at least one along every edge and is at most $D$ at the last line, which is equivalent to depth at most $D$.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.1, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_RefWPHP_LayeredRef

namespace RefWPHP

namespace Supplement

/-- The justification of a line of a Resolution refutation: a clause `ax A` of the formula, a
logical axiom `lem i` (`x_i ∨ ¬x_i`), a weakening `weak j` of the line `j`, or a resolvent
`res i j k` over `x_i` of the lines `j` (containing `x_i`) and `k` (containing `¬x_i`). Lines are
numbered from `0`. -/
inductive ResJust (n m : ℕ) : Type
  | ax (A : Fin m) : ResJust n m
  | lem (i : Fin n) : ResJust n m
  | weak (j : ℕ) : ResJust n m
  | res (i : Fin n) (j k : ℕ) : ResJust n m

/-- The premises a justification cites (the out-edges of its line in the refutation dag). -/
def ResJust.premises {n m : ℕ} : ResJust n m → List ℕ
  | ax _ => []
  | lem _ => []
  | weak j => [j]
  | res _ j k => [j, k]

/-- `ResLineOK φ lines t C J`: the clause `C` at line `t` of `lines` is correctly obtained by the
justification `J`. -/
def ResLineOK {n m : ℕ} (φ : Fin m → Finset (Lit n)) (lines : List (Finset (Lit n) × ResJust n m))
    (t : ℕ) (C : Finset (Lit n)) : ResJust n m → Prop
  | .ax A => C = φ A
  | .lem i => C = {(i, true), (i, false)}
  | .weak j => j < t ∧ ∃ D, (lines[j]?).map Prod.fst = some D ∧ D ⊆ C
  | .res i j k => j < t ∧ k < t ∧ ∃ Dj Dk, (lines[j]?).map Prod.fst = some Dj ∧
      (lines[k]?).map Prod.fst = some Dk ∧ (i, true) ∈ Dj ∧ (i, false) ∈ Dk ∧
      C = Dj.erase (i, true) ∪ Dk.erase (i, false)

/-- A Resolution refutation of the CNF `φ = C_1 ∧ ⋯ ∧ C_m` over `x_1, …, x_n`, N. Arteche,
*Resolution Lower Bounds versus the Weak Pigeonhole Principle*, STOC 2027 submission (held
manuscript, sha256 ee75d7f1…), §2.1.1, pp.13–14 (PDF 15–16): a sequence of clauses
`D_1, …, D_s` with `D_s = ⊥` (the empty clause), each `D_i` either (a) a clause of `φ`, (b) a
weakening `D_i ⊇ D_j` of an earlier clause, or (c) the resolvent `A ∨ B` of earlier clauses
`D_j = A ∨ x` and `D_k = B ∨ ¬x`; "we also allow the logical axiom `x ∨ ¬x`".
Each line records its clause together with its justification.

**Formalization Note.**
1. In (c), `A = D_j ∖ {x}` and `B = D_k ∖ {¬x}`, and the resolvent is exactly `A ∪ B`.
2. The justification is part of the object because the depth of a refutation is a property of its
   dag ("To every Resolution refutation π we can associate a directed acyclic graph in a natural
   way", p.14), which a bare list of clauses does not determine. -/
structure ResRefutation {n m : ℕ} (φ : Fin m → Finset (Lit n)) where
  /-- The lines: a clause and its justification. -/
  lines : List (Finset (Lit n) × ResJust n m)
  /-- Every line is correctly justified from `φ` and earlier lines. -/
  valid : ∀ (t : ℕ) (h : t < lines.length), ResLineOK φ lines t (lines[t]'h).1 (lines[t]'h).2
  /-- The last line is the empty clause. -/
  last : (lines.getLast?).map Prod.fst = some ∅

namespace ResRefutation

variable {n m : ℕ} {φ : Fin m → Finset (Lit n)}

/-- The length `length(π) = s`, the number of lines (p.14). -/
def length (π : ResRefutation φ) : ℕ := π.lines.length

/-- `π.DepthAtMost D`: the depth of `π`, the number of edges of the longest path in its dag from the
last line (the root, labelled `⊥`) to a line without premises (p.14), is at most `D`. Stated as the
existence of a labelling `h` of the lines that grows by at least one along every edge
(line `t` → each premise it cites) with `h(root) ≤ D`; the longest-path labelling shows that this is
equivalent to `depth(π) ≤ D`. -/
def DepthAtMost (π : ResRefutation φ) (D : ℕ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ (t : ℕ) (ht : t < π.lines.length),
      ∀ j ∈ (π.lines[t]'ht).2.premises, h j + 1 ≤ h t) ∧ h (π.lines.length - 1) ≤ D

end ResRefutation

end Supplement

end RefWPHP


