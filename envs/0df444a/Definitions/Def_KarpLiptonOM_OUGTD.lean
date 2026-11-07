-- Prove2me | Definitions.Def_KarpLiptonOM_OUGTD
-- name    : KarpLiptonOM_OUGTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:25.670549+00:00
-- url     : https://prove2.me/theorems/e8ac02d1-79e9-4a32-a49c-83a3b5d9358e
-- title:
--   $\mathrm{OUGTD}[\mathrm{FP}^X, \mathcal B, \mathrm P]$: unique-advice generator–tester–decoder computations
-- statement:
--   $L$ belongs to $\mathrm{OUGTD}[\mathrm{FP}^X, \mathcal B, \mathrm P]$ if it belongs to $\mathrm{OGTD}[\mathrm{FP}^X, \mathcal B, \mathrm P]$ via a generator $G$, a tester $T$ and a decoder $D$ such that, moreover, the tester accepts exactly one advice string for every length:
--   $$
--   |\mathrm{Acc}_T(n)| = 1 \quad \text{for every } n .
--   $$
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.10, p.24

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_PolyPred2
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- `OUGTD[FP^X, B, P]` (Definition A.2.10, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.24): as `OGTD`, and moreover `Acc_T(n)` has
exactly one element for every `n`. -/
def OUGTD (X : Set PromiseProblem) (B : Set (List Bool → List Bool → Prop)) :
    Set (Set (List Bool)) :=
  {L | ∃ PP ∈ X, ∃ (G : OracleTM) (k : ℕ) (p : Polynomial ℕ), G.IsPolyTime k ∧
    (∀ O, Consistent O PP → ∀ n : ℕ,
      (G.out O k (tupleEnc [List.replicate n true])).length = p.eval n) ∧
    ∃ T ∈ B, ∃ D : List Bool → List Bool → Prop, PolyPred2 D ∧ ∀ n : ℕ,
      (∀ O, Consistent O PP →
        T (List.replicate n true) (G.out O k (tupleEnc [List.replicate n true]))) ∧
      (∀ a, T (List.replicate n true) a →
        a.length = p.eval n ∧ ∀ x : List Bool, x.length = n → (D x a ↔ x ∈ L)) ∧
      ∃! a, T (List.replicate n true) a}

end KarpLiptonOM


