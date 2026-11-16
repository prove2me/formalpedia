-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_SuppressStep
-- name    : AgnosticTNS_Supplement_SuppressStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:47.505838+00:00
-- url     : https://prove2.me/theorems/2424041b-917d-4b78-9222-ebefe710720d
-- title:
--   Suppression step of the 3-centre construction
-- statement:
--   The **3-centre** of a torso is obtained by repeatedly suppressing peripheral vertices of degree at most $2$, never suppressing core vertices. One step: choose a non-core vertex $z$ with $\deg(z)\le2$; if $\deg(z)\in\{0,1\}$, delete $z$ and its incident edges; if $\deg(z)=2$ with incident neighbours $a$ and $b$, delete $z$ and its incident edges and, if $a\neq b$, add an edge $\{a,b\}$, preserving multiplicity.
--
--   **Formalization Note** A multigraph is a finite vertex set with a symmetric multiplicity matrix; $\deg(z)=\sum_{a\neq z}M(z,a)$. Degree $2$ with a single neighbour means one double edge, and then nothing is added.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.5, pp.48–49

import Mathlib

namespace AgnosticTNS.Supplement

/-- **One suppression step of the 3-centre construction**, Definition 6.5, pp.48–49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
A multigraph is a finite vertex set with a symmetric multiplicity matrix with zero diagonal. While some
non-core vertex `z` has degree at most `2`: if `deg(z) ∈ {0, 1}`, delete `z` and its edges; if
`deg(z) = 2` with incident neighbours `a`, `b`, delete `z` and its edges and, if `a ≠ b`, add an edge
`{a, b}` (preserving multiplicity). Core vertices are never suppressed.

**Formalization Note** `deg(z) = Σ_{a ≠ z} M(z, a)`. Degree `2` with a single neighbour `a` means
`M(z, a) = 2` (then `a = b` and no edge is added). The multiplicities of deleted vertices are left in
the matrix but no longer counted. -/
def SuppressStep {α : Type*} [DecidableEq α] (core : α → Prop) (A B : Finset α × (α → α → ℕ)) : Prop :=
  ∃ z ∈ A.1, ¬ core z ∧
    ((∑ a ∈ A.1.erase z, A.2 z a ≤ 1 ∧ B = (A.1.erase z, A.2)) ∨
      (∑ a ∈ A.1.erase z, A.2 z a = 2 ∧ (∃ a ∈ A.1.erase z, A.2 z a = 2) ∧ B = (A.1.erase z, A.2)) ∨
      (∑ a ∈ A.1.erase z, A.2 z a = 2 ∧ ∃ a ∈ A.1.erase z, ∃ b ∈ A.1.erase z, a ≠ b ∧ A.2 z a = 1 ∧
        A.2 z b = 1 ∧
        B = (A.1.erase z, fun u v => A.2 u v + if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then 1 else 0)))

end AgnosticTNS.Supplement


