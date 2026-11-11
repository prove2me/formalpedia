-- Prove2me | Definitions.Def_CircTrichotomy_BoolComb
-- name    : CircTrichotomy_BoolComb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:02.204429+00:00
-- url     : https://prove2.me/theorems/bfb2fd7d-43ee-4f3c-a1de-e9df446947c9
-- title:
--   Finite (positive) Boolean combinations inside $\Sigma^+$
-- statement:
--   Given a set $\mathcal G$ of languages, a **finite Boolean combination** of members of $\mathcal G$ is obtained from finitely many of them by complement (inside $\Sigma^+$), intersection and union; a **finite positive Boolean combination** uses only intersection and union. A **finite language** here is a finite subset of $\Sigma^+$.
--
--   All languages of the paper are positive (subsets of $\Sigma^+$), so the complement of $L$ is $\Sigma^+\setminus L$.
--
--   **Formalization Note** Both classes are inductive closures with binary $\cap$ and $\cup$; each member uses finitely many generators.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (5), p.3; Theorem 2.8 (6)–(7), p.6; p.16

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- Complement inside `Σ⁺`: `Σ⁺ \ L` (all languages are positive, p.16: "Unless stated otherwise we
will be working with positive languages"). -/
def posCompl {α : Type} (L : Language α) : Language α := {w | w ≠ [] ∧ w ∉ L}

/-- **Finite Boolean combination inside `Σ⁺`** of languages from `G` (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (5), p.3;
Theorem 2.8 (7), p.6; §A.4.3, p.18): the least class containing `G` and closed under complement
in `Σ⁺`, binary intersection and binary union. Every member is obtained in finitely many steps
from finitely many members of `G`. -/
inductive BoolComb {α : Type} (G : Set (Language α)) : Language α → Prop
  | base {L : Language α} : L ∈ G → BoolComb G L
  | compl {L : Language α} : BoolComb G L → BoolComb G (posCompl L)
  | inter {L M : Language α} : BoolComb G L → BoolComb G M → BoolComb G {w | w ∈ L ∧ w ∈ M}
  | union {L M : Language α} : BoolComb G L → BoolComb G M → BoolComb G {w | w ∈ L ∨ w ∈ M}

/-- **Finite positive Boolean combination** of languages from `G` (Theorem 2.8 (6), p.6): the least
class containing `G` and closed under binary intersection and binary union. -/
inductive PosBoolComb {α : Type} (G : Set (Language α)) : Language α → Prop
  | base {L : Language α} : L ∈ G → PosBoolComb G L
  | inter {L M : Language α} : PosBoolComb G L → PosBoolComb G M →
      PosBoolComb G {w | w ∈ L ∧ w ∈ M}
  | union {L M : Language α} : PosBoolComb G L → PosBoolComb G M →
      PosBoolComb G {w | w ∈ L ∨ w ∈ M}

/-- A finite positive language: a finite subset of `Σ⁺`. -/
def IsFinitePosLang {α : Type} (L : Language α) : Prop := Set.Finite (L : Set (List α)) ∧ [] ∉ L

end CircTrichotomy


