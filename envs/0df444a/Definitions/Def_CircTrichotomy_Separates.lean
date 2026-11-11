-- Prove2me | Definitions.Def_CircTrichotomy_Separates
-- name    : CircTrichotomy_Separates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:39.356704+00:00
-- url     : https://prove2.me/theorems/387dc32b-22e4-4610-b0b1-b9b8026612b5
-- title:
--   A circuit separates a pair of words
-- statement:
--   A single-output $n$-circuit $C$ over $\Sigma$ **separates** the pair $(x,y)\in\Sigma^n\times\Sigma^n$ if $x\in L(C)$ and $y\notin L(C)$.
--
--   It is the notion of the gate-counting lower bound.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition C.7, p.45

import Mathlib
import Definitions.Def_CircTrichotomy_Circuit

set_option autoImplicit false

namespace CircTrichotomy

/-- **A circuit separates a pair of words** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition C.7, p.45): "An n-circuit C over the
alphabet Σ separates a pair of words (x, y) ∈ Σⁿ × Σⁿ if x ∈ L(C) and y ∉ L(C)." (§C.2: "all
circuits are assumed to have precisely one output gate".) -/
def Separates {α : Type} {n : ℕ} (C : Circuit α n 1) (x y : List α) : Prop :=
  C.AcceptsList x ∧ ¬ C.AcceptsList y

end CircTrichotomy


