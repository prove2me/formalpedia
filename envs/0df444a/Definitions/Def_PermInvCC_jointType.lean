-- Prove2me | Definitions.Def_PermInvCC_jointType
-- name    : PermInvCC_jointType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:59.837775+00:00
-- url     : https://prove2.me/theorems/b519af15-d9bd-4e28-b45d-1020c2fb7732
-- title:
--   Joint type $T_{ab}=|\{i:(x_i,y_i)=(a,b)\}|$, margins and histograms
-- statement:
--   The **joint type** of $(x,y)\in[q]^n\times[q]^n$ is the $q\times q$ table
--   $$T_{ab}:=|\{i:(x_i,y_i)=(a,b)\}|\qquad(a,b\in[q]).$$
--   Its **row margins** are $\rho_a=\sum_b T_{ab}$ and its **column margins** $\sigma_b=\sum_a T_{ab}$. The **histogram** of a string $x$ is $a\mapsto|\{i:x_i=a\}|$; the histograms of $x$ and $y$ are the margins of their joint type, and each has total $n$.
--
--   A *type of total $n$* is any table of nonnegative integers with entry sum $n$; every such table is the joint type of some pair.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.3, p.9

import Mathlib

namespace PermInvCC

/-- The **joint type** of `(x, y) ∈ [q]ⁿ × [q]ⁿ`: the table
`T_{ab} = |{i : (x_i, y_i) = (a, b)}|` (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, Definition 2.3, p.9). A *type of total `n`* is any table
`T : [q] × [q] → ℕ` with entry sum `n`; every such table is the joint type of some pair. -/
def jointType {n q : ℕ} (x y : Fin n → Fin q) : Fin q → Fin q → ℕ :=
  fun a b => (Finset.univ.filter fun i => x i = a ∧ y i = b).card

/-- The **row margins** `ρ_a = ∑_b T_{ab}` of a table (Definition 2.3, p.9). -/
def rowMargin {q : ℕ} (T : Fin q → Fin q → ℕ) (a : Fin q) : ℕ := ∑ b, T a b

/-- The **column margins** `σ_b = ∑_a T_{ab}` of a table (Definition 2.3, p.9). -/
def colMargin {q : ℕ} (T : Fin q → Fin q → ℕ) (b : Fin q) : ℕ := ∑ a, T a b

/-- The **histogram** of a string `x ∈ [q]ⁿ`: `a ↦ |{i : x_i = a}|` (Definition 2.3, p.9; the
histograms of `x` and `y` are the row and column margins of their joint type). -/
def hist {n q : ℕ} (x : Fin n → Fin q) (a : Fin q) : ℕ :=
  (Finset.univ.filter fun i => x i = a).card

end PermInvCC


