-- Prove2me | Definitions.Def_LawLocalComp_clauseU3
-- name    : LawLocalComp_clauseU3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:23.52211+00:00
-- url     : https://prove2.me/theorems/19856eda-bd6d-493f-9bee-5d1e2a0fcb1f
-- title:
--   Theorem 1.1, row 3 upper: both resources, order $J(\varepsilon,N,q)$
-- statement:
--   As row 1, under both a horizon $N$ and a rank promise $q$ with $Q=\min\{N,q\}\ge2$: maps $\Phi_{\varepsilon,N,q}$ with at most $C\,J(\varepsilon,N,q)$ atoms satisfying (1), computable in time polynomial in the input bits, $1/\varepsilon$, $\log N$ and $\log q$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Mixed-resource upper in Theorem 1.1", p.7

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_Jfun

namespace LawLocalComp

/-- **Row 3 upper of Theorem 1.1 (both resources, order `J(ε, N, q)`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

As row 1, under both a horizon `N` and a rank promise `q` with `Q = min{N, q} ≥ 2`, with at most
`C J(ε, N, q)` atoms.
-/
def clauseU3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × ℕ × ℕ → Law → Law,
    PolyLawMap (fun p => [p.1, (p.2.1 : ℚ), (p.2.2 : ℚ)]) (fun p => ⌈1 / p.1⌉₊) (fun _ => True) Φ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ N q : ℕ, 2 ≤ min N q →
      (∀ X : Law, IsRatLaw X → IsGoodOutput X (Φ (ε, N, q) X) ∧
        ((Φ (ε, N, q) X).w.support.card : ℝ) ≤ C * Jfun ε N q) ∧
      Contract (Φ (ε, N, q)) (.both N q) (fun _ => True) (1 + ε)

end LawLocalComp


