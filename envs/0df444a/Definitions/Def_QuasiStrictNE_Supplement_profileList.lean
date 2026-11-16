-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_profileList
-- name    : QuasiStrictNE_Supplement_profileList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:41:20.732366+00:00
-- url     : https://prove2.me/theorems/387dd51e-5e16-4b28-9a2b-fab7c50be522
-- title:
--   All pure strategy profiles in lexicographic order
-- statement:
--   For action counts $k_0,\dots,k_{n-1}$, this is the list of all pure strategy profiles $s = (s_0,\dots,s_{n-1})$, $s_j \in \{0,\dots,k_j-1\}$, each listed once, in lexicographic order with player $0$ most significant.
--
--   It fixes the order in which the payoff table of a strategic-form game is written in its binary code.
--
--   **Formalization Note** The paper fixes no order. Any fixed order gives the same decision problem up to a polynomial-time re-encoding.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19 (games in strategic form)

import Mathlib

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **All pure strategy profiles in lexicographic order** (used to write the payoff table of a game in
strategic form, Hansen & Nie, arXiv:2611.06350, Theorem 2, p.19).

`profileList n k` lists every `s : (i : Fin n) → Fin (k i)` exactly once, in lexicographic order with
player `0` most significant: for `n = 0` the single empty profile; for `n + 1`, for each action `a` of
player `0` in increasing order, the profiles `Fin.cons a s` with `s` running over `profileList n` of
the remaining players.

**Formalization Note** The paper fixes no order of the payoff table; any fixed order gives the same
problem up to a polynomial-time re-encoding. -/
def profileList : (n : ℕ) → (k : Fin n → ℕ) → List ((i : Fin n) → Fin (k i))
  | 0, _ => [fun i => i.elim0]
  | n + 1, k =>
      (List.finRange (k 0)).flatMap fun a =>
        (profileList n (fun i => k i.succ)).map fun s =>
          (Fin.cons a s : (i : Fin (n + 1)) → Fin (k i))

end QuasiStrictNE.Supplement


