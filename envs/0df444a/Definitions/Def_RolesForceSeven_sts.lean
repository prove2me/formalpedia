-- Prove2me | Definitions.Def_RolesForceSeven_sts
-- name    : RolesForceSeven_sts
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-24T05:40:40.292098+00:00
-- url     : https://prove2.me/theorems/ae802aab-f5a6-44b0-88f2-3edd5f35be90
-- title:
--   Steiner triple systems on $n$ points and role colourings
-- statement:
--   Fix $n \in \mathbb{N}$ and take the points $[n] = \{0, 1, \dots, n-1\}$. A **Steiner triple system** on $[n]$ is a finite family $\mathcal{L}$ of subsets of $[n]$, called **lines**, such that
--
--   1. every line has exactly $3$ points, and
--   2. every two distinct points $x \neq y$ lie together on exactly one line.
--
--   A **role colouring** of such a system is a function $\rho$ assigning to each point $x$ and each line $\ell$ a role $\rho(x, \ell) \in \{0, 1, 2\}$, such that
--
--   1. the three points of each line receive three different roles;
--   2. **completeness:** for every point $x$ and every role $r$ there is a line $\ell \ni x$ with $\rho(x, \ell) = r$;
--   3. **minimality:** two different lines through the same point $x$ give $x$ different roles.
--
--   **Formalization Note** Points are `Fin n` and lines are `Finset (Fin n)`. The role function has type `Fin n → Finset (Fin n) → Fin 3`; only its values $\rho(x, \ell)$ with $\ell$ a line and $x \in \ell$ are constrained. No condition is placed on $n$, so the empty system ($n = 0$, no lines) is allowed.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §3, Definition 3.1 (Steiner triple system) and Definition 3.5 (role colouring): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Section 3: https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md ; public references: Wikipedia, "Steiner system" (Steiner triple systems, replication number): https://en.wikipedia.org/wiki/Steiner_system ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane ; Wikipedia, "Octonion" (Fano plane mnemonic for the multiplication of imaginary units): https://en.wikipedia.org/wiki/Octonion

import Mathlib

namespace RolesForceSeven

/-- A Steiner triple system on the points `Fin n`: every line has three points,
and every pair of distinct points lies on exactly one line. -/
structure STS (n : ℕ) where
  lines : Finset (Finset (Fin n))
  card_three : ∀ l ∈ lines, l.card = 3
  pair_unique : ∀ x y : Fin n, x ≠ y → ∃! l, l ∈ lines ∧ x ∈ l ∧ y ∈ l

/-- A role colouring (C1 Definition 3.5). `role x l` is the role of point `x` on
line `l`; only its values for `x ∈ l ∈ lines` matter. -/
def RoleColouring {n : ℕ} (S : STS n) (role : Fin n → Finset (Fin n) → Fin 3) :
    Prop :=
  -- the three points of a line get different roles
  (∀ l ∈ S.lines, ∀ x ∈ l, ∀ y ∈ l, role x l = role y l → x = y) ∧
  -- completeness: every point takes every role at least once
  (∀ x : Fin n, ∀ ρ : Fin 3, ∃ l ∈ S.lines, x ∈ l ∧ role x l = ρ) ∧
  -- minimality: every point takes every role at most once
  (∀ x : Fin n, ∀ l ∈ S.lines, ∀ l' ∈ S.lines, x ∈ l → x ∈ l' →
      role x l = role x l' → l = l')

end RolesForceSeven


