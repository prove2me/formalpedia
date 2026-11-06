-- Prove2me | Definitions.Def_LawLocalComp_clauseU2
-- name    : LawLocalComp_clauseU2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:23.115901+00:00
-- url     : https://prove2.me/theorems/9acc1432-c543-4750-bfea-001027ef594e
-- title:
--   Theorem 1.1, row 2 upper: rank $q$ only, order $\varepsilon^{-1}\log(q+1)$
-- statement:
--   As row 1, under a rank promise $q\ge2$ alone (every finite selection whose directions span at most $q$ dimensions, of any size): maps $\Phi_{\varepsilon,q}$ with at most $C\,\varepsilon^{-1}\log(q+1)$ atoms satisfying (1), computable in time polynomial in the input bits, $1/\varepsilon$ and $\log q$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Endpoint transfer", p.7

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap

namespace LawLocalComp

/-- **Row 2 upper of Theorem 1.1 (rank `q` only, order `ε^{-1} log(q+1)`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

As row 1, under a rank promise `q ≥ 2` alone (every finite selection whose directions span at most
`q` dimensions), with at most `C ε^{-1} log(q + 1)` atoms.
-/
def clauseU2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × ℕ → Law → Law,
    PolyLawMap (fun p => [p.1, (p.2 : ℚ)]) (fun p => ⌈1 / p.1⌉₊) (fun _ => True) Φ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, 2 ≤ q →
      (∀ X : Law, IsRatLaw X → IsGoodOutput X (Φ (ε, q) X) ∧
        ((Φ (ε, q) X).w.support.card : ℝ) ≤ C * (1 / (ε : ℝ)) * Real.log (q + 1)) ∧
      Contract (Φ (ε, q)) (.rank q) (fun _ => True) (1 + ε)

end LawLocalComp


