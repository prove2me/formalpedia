-- Prove2me | Definitions.Def_N25_CanonicalPointPlaces
-- name    : N25_CanonicalPointPlaces
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:11:00.362608+00:00
-- url     : https://prove2.me/theorems/70669280-e3ef-407f-bdc4-d1c106d2722d
-- title:
--   Canonical points and degree-one places at the good primes
-- statement:
--   Let $p∈\{2,3\}$, let $K$ be a perfect field of characteristic $p$, and let $X_K$ be the canonical projective level-$25$ curve. The file defines an equivalence $$X_K(K)_{\mathrm{norm}}\simeq\{P\text{ a place of }K(X_K):\deg P=1\},$$ where the left side is the full first-nonzero-coordinate projective point carrier, including every boundary chart. This identifies the executable projective points used in the finite-field counts with degree-one places of the canonical function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalSchemePlaces
import Definitions.Def_N25_CanonicalSchemePoints
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_CanonicalSchemePointCharts
import Theorems.Thm_N25_canonicalOpenChartRing_isDomain_good25
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! The full normalized canonical point carrier corresponds to degree-one places. -/
noncomputable section
universe u
namespace N25.Endgame
open N25

/-- The signed full projective point/place equivalence, including every boundary chart. -/
def canonicalPointPlaceEquivGood25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type u) [Field K] [PerfectField K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    CanonicalPoint25 K ≃
      {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} := by
  letI : IsDomain (CanonicalOpenChartRing25 K) :=
    canonicalOpenChartRing_isDomain_good25 p hp K
  exact (canonicalNormalizedSchemePointEquiv25 K).trans
    (canonicalSchemePointPlaceEquivGood25 p hp K)

end N25.Endgame


