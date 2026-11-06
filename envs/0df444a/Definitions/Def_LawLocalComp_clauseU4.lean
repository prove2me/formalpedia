-- Prove2me | Definitions.Def_LawLocalComp_clauseU4
-- name    : LawLocalComp_clauseU4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:43.357067+00:00
-- url     : https://prove2.me/theorems/ac1ec6dd-d04d-45b2-ad12-3d13e09cf423
-- title:
--   Theorem 1.1, row 4 upper: lattice-LC or conditional-IFR laws, order $A(\varepsilon,M)$
-- statement:
--   There are an absolute constant $C>0$ and maps $\Phi_{\varepsilon,R}$, computable in time polynomial in the input bits, $1/\varepsilon$ and the bit lengths of the supplied resources on conditional-IFR inputs, such that for rational $0<\varepsilon\le1$ and every resource $R$ with $M\ge2$: on every conditional-IFR law (in particular every lattice-log-concave law) the output is a rational conditional-mean replacement preserving mean and point masses with at most $C\,A(\varepsilon,M)$ atoms, and (1) holds for every admitted selection of conditional-IFR laws.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "LC accuracy upper in Theorem 1.1", pp.14–15, and Corollary 8.2, p.16

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsCondIFR
import Definitions.Def_LawLocalComp_Afun
import Definitions.Def_LawLocalComp_Resource_M
import Definitions.Def_LawLocalComp_Resource_params

namespace LawLocalComp

/-- **Row 4 upper of Theorem 1.1 (lattice-LC or conditional-IFR laws, order `A(ε, M)`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

For every supplied resource `R` with `M ≥ 2` (`M = N`, `q` or `min{N, q}`), a polynomial-time map
on conditional-IFR lattice laws (which contain the lattice-log-concave laws) with at most `C A(ε, M)`
atoms satisfying (1) on selections of such laws. Corollary 8.2, p.16, extends the LC upper to this
class.
-/
def clauseU4 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × Resource → Law → Law,
    PolyLawMap (fun p => p.1 :: p.2.params) (fun p => ⌈1 / p.1⌉₊) IsCondIFR Φ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ R : Resource, 2 ≤ R.M →
      (∀ X : Law, IsCondIFR X → IsGoodOutput X (Φ (ε, R) X) ∧
        ((Φ (ε, R) X).w.support.card : ℝ) ≤ C * Afun ε R.M) ∧
      Contract (Φ (ε, R)) R IsCondIFR (1 + ε)

end LawLocalComp


