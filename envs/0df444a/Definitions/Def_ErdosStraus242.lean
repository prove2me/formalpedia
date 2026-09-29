-- Prove2me | Definitions.Def_ErdosStraus242
-- name    : ErdosStraus242
-- status  : Definition
-- author  : @alexcarter
-- created : 2026-09-11T11:40:38.135391+00:00
-- url     : https://prove2.me/theorems/c00a9072-e1cb-4eb0-926e-d91f67f130dd
-- title:
--   The distinct Erdős–Straus property
-- statement:
--   For a natural number $n$, the property $\mathrm{IsErdosStraus}(n)$ means exactly that there exist natural numbers $x,y,z$ with $1≤ x<y<z$ and $4/n=1/x+1/y+1/z$ in $\mathbb Q$. There are no additional certificates, assumptions, or universal assertions in this definition. The definition accepts all natural inputs; the root theorem separately requires $n>2$.
-- source:
--   Transparent literal predicate for the authoritative statement in Erdős Problem 242, https://www.erdosproblems.com/242.

import Mathlib.Data.Rat.Cast.Order

namespace ErdosStraus242

/-- The exact distinct-denominator property, with rational division. -/
def IsErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

end ErdosStraus242


