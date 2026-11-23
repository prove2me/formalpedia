-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch
-- name    : CorrelatedAuctionComplexity_Main_NashFixedSearch
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T07:11:34.8337+00:00
-- url     : https://prove2.me/theorems/e2faff3b-ca0b-45d6-b106-5e4b780619bf
-- title:
--   Rational weak fixed points of the HDFPA Nash map
-- statement:
--   This interface has two parts. First, `ExpectedUtilityPolytime` records the uniform exact arithmetic algorithm from Lemma 15: a Cook machine computes the rational expected utility $U_i(\sigma)$ of every legal rational profile in a normalized HDFPA, and its output agrees with the real finite-expectation definition.
--
--   Second, for an HDFPA $H$ with $k=|B|$ bids and accuracy $\eta>0$, `hNashFixedSearch` asks for a rational legal profile $\sigma$ satisfying the weak approximate fixed-point condition
--   $$
--   \left|F_H(\sigma)_{i,b}-\sigma_{i,b}\right|
--   \le \frac{\eta^2}{16k^3}
--   \qquad(i\in N,\ b\in B),
--   $$
--   where $F_H$ is Nash's map from equation (6). The valid instances are exactly those of the variable-accuracy HDFPA equilibrium problem, and answers have the same polynomial witness bound. Canonical profile decoding and legality are part of the answer relation, so fixed points are sought on the no-overbidding product simplex used by the source.
--
--   **Formalization Note** The source's non-strict weak approximation inequality is used literally. The expected-utility condition is a proposition rather than an algorithmic assumption hidden in the search problem; membership lemmas take it as an explicit hypothesis and discharge it with Lemma 15.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemmas 15–16, Section 4.7, pp. 19–21, especially equation (6) and the tolerance η²/(16|B|³) on p. 20.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

/-- The uniform polynomial-time exact expected-utility interface of Lemma 15. -/
def ExpectedUtilityPolytime : Prop :=
  ∃ f : Bits → Bits, CookPvsNP.PolyTimeComputable f ∧
    ∀ (n : ℕ) (H : HDFPA (Fin n)), H.WellFormed 1 →
      ∀ (σ : H.RatProfile), H.Legal (H.realProfile σ) → ∀ i : Fin n,
        f (utilityRequest H σ i) = encodeRat (H.utilityQ σ i) ∧
          (H.utilityQ σ i : ℝ) = H.utility (H.realProfile σ) i

/-- Rational weak approximate fixed points of Nash's HDFPA map, with the same
instances and polynomial answer-size bound as the equilibrium search problem. -/
noncomputable def hNashFixedSearch : TetrisHard.Rows.SearchProblem where
  valid s := hVariableAccuracy.valid s
  answer s t := ∃ ε a, splitAccuracy s = some (ε,a) ∧ 0 < ε ∧
    ∃ (n : ℕ) (H : HDFPA (Fin n)) (p : H.RatProfile),
      decodeH a = some ⟨n,H⟩ ∧ H.WellFormed 1 ∧
      t.length ≤ witnessBound a ε ∧ decodeHProfile H t = some p ∧
      H.Legal (H.realProfile p) ∧
      ∀ i b, |H.nashMap (H.realProfile p) i b - H.realProfile p i b| ≤
        nashMapTolerance (ε : ℝ) H.bids.card

end CorrelatedAuctionComplexity.Main


