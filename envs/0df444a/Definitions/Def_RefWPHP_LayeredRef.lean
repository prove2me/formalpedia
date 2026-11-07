-- Prove2me | Definitions.Def_RefWPHP_LayeredRef
-- name    : RefWPHP_LayeredRef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:25.668454+00:00
-- url     : https://prove2.me/theorems/5a9faec5-c24c-435d-8e06-2a028dc98adf
-- title:
--   Layered Resolution refutations of a CNF, with layers $\pi_1, \dots, \pi_D$ and a separate root
-- statement:
--   Let $\varphi = C_1 \wedge \dots \wedge C_m$ be a CNF over $x_1, \dots, x_n$, with clauses as sets of literals. A **layered Resolution refutation** $\pi$ of $\varphi$ with layers of at most $L$ clauses and depth $D \ge 1$ assigns to each layer $k \in [D]$ a set of slots in $[L]$, each slot holding a clause, such that every clause $C$ of layer $k$ is one of the following:
--
--   1. a weakening of an axiom: $C_A \subseteq C$ for some $A \in [m]$;
--   2. derived over $x_i$ from clauses $\mathrm{left}_\pi(C)$ and $\mathrm{right}_\pi(C)$ of layer $k+1$: $(\mathrm{left}_\pi(C) \setminus \{x_i\}) \cup (\mathrm{right}_\pi(C) \setminus \{\neg x_i\}) \subseteq C$.
--
--   The final empty clause $C_\emptyset$ is not in any layer. It is resolved over a variable $x_{i_\emptyset}$ from two clauses of layer $1$, whose reduced union is empty.
--
--   This is the object the substitution $\sigma_{\pi,s}$ compresses: slot numbers are the pigeons of $\mathrm{PHP}^L_W$, and one pigeon set serves all layers.
--
--   **Formalization Note** Layer $k$ of Lean's `Fin D` is the paper's $\pi_{k+1}$. $L$ bounds each layer rather than the total length, leaves may sit in any layer, and a resolvent need only contain the union of the reduced premises; the page's refutation is an instance. A weakening from a non-axiom $C_0$ is a derivation with $\mathrm{left}_\pi(C) = \mathrm{right}_\pi(C) = C_0$ (p.19). Leaves are weakenings of axioms of $\varphi$: the logical axioms $x \vee \neg x$ allowed on p.14 can be removed without changing the layers, $L$ or $D$. Unsatisfiability of $\varphi$ is implied by the structure and is not a field.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3.1, p.19 (PDF p.21), root p.20 (PDF p.22)

import Mathlib

namespace RefWPHP

/-- A literal over the variables `x_1, …, x_n` (0-based): `(i, true)` is `x_i` and `(i, false)` is
`¬x_i`. `Lit n` is the set `Lit_n` of N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), p.16. -/
abbrev Lit (n : ℕ) : Type := Fin n × Bool

/-- How a slot of a layered refutation is obtained: as a weakening `ax A` of the clause `A` of `φ`,
or by resolving `res i l r` over `x_i` from the slot `l` (left premise, which carries the positive
pivot `x_i`) and the slot `r` (right premise, negative pivot) of the next layer. -/
inductive RStep (n m L : ℕ) : Type
  | ax (A : Fin m) : RStep n m L
  | res (i : Fin n) (l r : Fin L) : RStep n m L
  deriving DecidableEq

/-- A layered Resolution refutation of the CNF `φ = C_1 ∧ ⋯ ∧ C_m` (clauses as sets of literals)
with layers of at most `L` clauses and depth `D`, in the sense of §3.1, p.19 (PDF 21), and the
root of p.20 (PDF 22).

Layer `k : Fin D` is the paper's `π_{k+1}`; its clauses occupy the slots `C : Fin L` with
`used k C`, a slot's number being its value under the paper's injection of the layer into `[L]`.
A used slot is either a weakening of an axiom of `φ` (`φ_A ⊆ C`), or the resolvent over `x_i` of
two used slots of the next layer: the left premise without `x_i` and the right premise without
`¬x_i` are contained in `C` (p.14 rule (Res), with weakening). The final empty clause `C_∅` is not
in any layer; it is resolved over `x_{i_∅}` from two used slots of layer `0` (the paper's `π_1`).

**Formalization Note.**
1. `L` bounds the number of clauses of each layer, rather than the total length; every
   refutation of length `L` has layers of at most `L` clauses.
2. Leaves may sit in any layer, and a resolvent need only contain the union of the reduced
   premises. A weakening from a non-axiom clause `C_0` is `res i C_0 C_0` (p.19: `left(C) =
   right(C) = C_0`).
3. Leaves are weakenings of axioms of `φ`. The logical axioms `x ∨ ¬x` that p.14 allows "for the
   sake of completeness" are not leaves: the proof of (3.23), p.23, uses that every underived
   clause weakens an axiom of `φ`. They can be removed without changing the layers, `L` or `D`: a
   non-tautological resolvent of `x ∨ ¬x` (pivot `x`) and `B` contains `B`, so it becomes a
   weakening of `B`, and a resolvent with any other tautological premise is itself a tautology.
4. A weakening from a non-axiom carries a pivot `i` (any variable); this needs `n ≥ 1`, which the
   root pivot provides. The final inference is a resolution over a variable, as p.20 takes it.
5. Unsatisfiability of `φ` is implied by the structure. -/
structure LayeredRef {n m : ℕ} (φ : Fin m → Finset (Lit n)) (L D : ℕ) where
  /-- Which slots of each layer hold a clause of the refutation. -/
  used : Fin D → Fin L → Bool
  /-- The clause held in a slot. -/
  clause : Fin D → Fin L → Finset (Lit n)
  /-- How the clause of a slot is obtained. -/
  step : Fin D → Fin L → RStep n m L
  /-- The pivot `x_{i_∅}` of the final inference. -/
  rootPivot : Fin n
  /-- The slot of `C_∅^left` in layer `0`. -/
  rootLeft : Fin L
  /-- The slot of `C_∅^right` in layer `0`. -/
  rootRight : Fin L
  pos_depth : 0 < D
  ax_ok : ∀ (k : Fin D) (C : Fin L) (A : Fin m),
    used k C = true → step k C = RStep.ax A → φ A ⊆ clause k C
  res_ok : ∀ (k : Fin D) (C : Fin L) (i : Fin n) (l r : Fin L),
    used k C = true → step k C = RStep.res i l r →
      ∃ h : k.val + 1 < D, used ⟨k.val + 1, h⟩ l = true ∧ used ⟨k.val + 1, h⟩ r = true ∧
        (clause ⟨k.val + 1, h⟩ l).erase (i, true) ∪ (clause ⟨k.val + 1, h⟩ r).erase (i, false)
          ⊆ clause k C
  root_ok : used ⟨0, pos_depth⟩ rootLeft = true ∧ used ⟨0, pos_depth⟩ rootRight = true ∧
    (clause ⟨0, pos_depth⟩ rootLeft).erase (rootPivot, true) ∪
      (clause ⟨0, pos_depth⟩ rootRight).erase (rootPivot, false) = ∅

end RefWPHP


