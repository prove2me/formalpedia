-- Prove2me | Definitions.Def_RobustBoolPCSP_FixingSet
-- name    : RobustBoolPCSP_FixingSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:01.398216+00:00
-- url     : https://prove2.me/theorems/2a6ebdb5-222a-450d-9a7d-f6cb38d41c02
-- title:
--   Fixing sets and odd parities of Boolean operations
-- statement:
--   For an operation $F:\{0,1\}^L\to\{0,1\}$ write $F(S)$ for its value on the indicator vector of a set $S\subseteq[L]$ of input positions. A set $J\subseteq[L]$ is a **fixing set** of $F$ if
--
--   $$F(S)=0\ \text{ whenever } S\cap J=\emptyset,\qquad F(S)=1\ \text{ whenever } J\subseteq S.$$
--
--   $F$ is an **odd parity** if $F(S)=|S\cap T|\bmod 2$ for all $S$, for some $T\subseteq[L]$ of odd size.
--
--   These are the two alternatives in the hypothesis of the bounded-fixing-set obstruction (Theorem 2.2).
--
--   **Formalization Note** Both halves of the fixing-set definition are required; this differs from the published one-sided `SymBoolPCSP.CFixing.IsCFixing`.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.1, p.7 (folded, idempotent, fixing set, odd parity)

import Mathlib
import Definitions.Def_SymBoolPCSP_CFixing_Basic

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing

/-- `J` is a **fixing set** of `F : {0,1}^L → {0,1}` (§2.1, p.7): "Write F(S) for its value on the
indicator of a set of input positions. A fixing set J forces F(S) = 0 when S ∩ J = ∅ and F(S) = 1
when J ⊆ S."

**Formalization Note.** Both halves of the paper's definition are required. This is not the
published `SymBoolPCSP.CFixing.IsCFixing`, which has only the first half. `F(S)` is `F` applied to
the indicator vector `SymBoolPCSP.CFixing.indicator S` (`true` = 1). -/
def IsFixingSet {L : ℕ} (F : (Fin L → Bool) → Bool) (J : Finset (Fin L)) : Prop :=
  (∀ S : Finset (Fin L), Disjoint S J → F (indicator S) = false) ∧
    (∀ S : Finset (Fin L), J ⊆ S → F (indicator S) = true)

/-- `F` is an **odd parity** (§2.1, p.7): "An odd parity has the form F(S) = |S ∩ T| mod 2 for an
odd-size set T." -/
def IsOddParity {L : ℕ} (F : (Fin L → Bool) → Bool) : Prop :=
  ∃ T : Finset (Fin L), Odd T.card ∧
    ∀ S : Finset (Fin L), F (indicator S) = decide ((S ∩ T).card % 2 = 1)

end RobustBoolPCSP


