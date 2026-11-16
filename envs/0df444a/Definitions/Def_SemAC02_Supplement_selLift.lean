-- Prove2me | Definitions.Def_SemAC02_Supplement_selLift
-- name    : SemAC02_Supplement_selLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:45:31.044573+00:00
-- url     : https://prove2.me/theorems/eab70aeb-a98a-4b12-be3a-38d793368b24
-- title:
--   The selector lift Lift_q(F)
-- statement:
--   For a CNF $F$ on $y_1,\dots,y_n$ and $q\ge2$, $\mathrm{Lift}_q(F)$ has variables $X_{i,b,a}$ ($i\in[n]$, $b\in\{0,1\}$, $a\in[q]$) and the clauses
--
--   1. the selector clause $\bigvee_{b,a}X_{i,b,a}$ for each $i$;
--   2. the exclusion clause $\neg X_{i,b,a}\vee\neg X_{i,b',a'}$ for every pair of distinct cells of block $i$;
--   3. for each $C\in F$, the clause obtained by replacing $y_i$ with $\bigvee_aX_{i,1,a}$ and $\neg y_i$ with $\bigvee_aX_{i,0,a}$.
--
--   Theorems 7.9 and 7.12 concern this formula; $G_n=\mathrm{Lift}_n(F_n)$.
--
--   **Formalization Note** CNFs are lists of clauses (clauses counted with multiplicity).
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §7.3.2, p.55 (PDF p.57); p.58 (PDF p.60)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02.Supplement

open LiftSAParity

/-- The **selector lift** `Lift_q(F)` of a CNF `F` on `y₁, …, y_n` (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §7.3.2, p.55): variables `X_{i,b,a}` (`i ∈ [n]`, `b ∈ {0,1}`, `a ∈ [q]`) and the
clauses

1. the selector clause `⋁_{b,a} X_{i,b,a}` for each block `i`;
2. the exclusion clause `¬X_{i,b,a} ∨ ¬X_{i,b',a'}` for every pair of distinct cells of block `i`;
3. for each `C ∈ F`, the clause obtained by replacing `y_i` by `⋁_a X_{i,1,a}` and `¬y_i` by
   `⋁_a X_{i,0,a}`.

**Formalization Note** The CNF `F` and its lift are lists of clauses, so clauses are counted with
multiplicity; the colour `b` is a `Bool` (`true` = 1). -/
noncomputable def selLift {n : ℕ} (q : ℕ) (F : List (Clause (Fin n))) : List (Clause (Fin n × Bool × Fin q)) :=
  (List.finRange n).map (fun i => Finset.univ.image (fun c : Bool × Fin q => ((i, c), true))) ++
  (List.finRange n).flatMap (fun i =>
    (((Finset.univ : Finset (Finset (Bool × Fin q))).filter (fun S => S.card = 2)).toList).map
      (fun S => S.image (fun c => ((i, c), false)))) ++
  F.map (fun C => C.biUnion (fun l =>
    Finset.univ.image (fun a : Fin q => ((l.1, l.2, a), true))))

end SemAC02.Supplement


