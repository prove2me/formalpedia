-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_Supplement_PureDecision
-- name    : CorrelatedAuctionComplexity_Main_Supplement_PureDecision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:51.328032+00:00
-- url     : https://prove2.me/theorems/35830d69-a0b0-4ea9-a927-ed6abc999298
-- title:
--   Pure HDFPA equilibrium decision language and effective accuracy prescriptions
-- statement:
--   Let $\delta:\mathbb N\to\mathbb Q$ prescribe the approximation tolerance at each input bit length. It is polynomial-time evaluable when an actual polynomial-time machine, on every binary string $s$, outputs the published binary rational code of $\delta(|s|)$. Runtime is measured in $|s|$, as for the auction input.
--
--   The pure-equilibrium existence language is
--
--   $$L_\delta=\{s:\operatorname{decodeH}(s)=H,\ H\text{ is well formed with bids and values in }[0,1],\ \exists\sigma\text{ pure and legal},\ U_i(\sigma)\ge U_i(b,\sigma_{-i})-\delta(|s|)W_i\text{ for all }i,\ b\in B_i\}.$$
--
--   Here $B_i$ consists of the permitted bids no larger than bidder $i$'s value; $W_i$ is the sum of weights of incident hyperedge occurrences, and utilities use the published uniform-tie first-price payoff. Malformed strings and codes of auctions failing the source's standing assumptions are outside the language. All finite bid sets, positive rational edge weights and nonempty hyperedges allowed by the base model are included, with no bound on hyperedge size and no requirement that weights sum to one.
--
--   The threshold family is $\theta_{c,k}(N)=1/(c(N+1)^k)$ for positive integer parameters $c,k$. This interface separates the decision language from the existing mixed-equilibrium search relations and supports Theorem 21 without assuming either hardness or equilibrium existence. Mathematical profiles use real probabilities; pure legal profiles are precisely deterministic choices of one allowed bid per bidder.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Section 3.2, pp.10–11 (PDF pp.10–11), Definition 4, p.11 (PDF p.11); Appendix A, Theorem 21, p.28 (PDF p.28), proof p.29 (PDF p.29).

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main.Supplement

/-- An effective rational accuracy prescription, evaluated from the input's bit length.
The runtime is polynomial in that length, rather than in its binary logarithm. -/
def PolynomialAccuracy (δ : ℕ → ℚ) : Prop :=
  CookPvsNP.PolyTimeComputable (fun s : Bits => encodeRat (δ s.length))

/-- A reciprocal-polynomial threshold. Theorem 21 quantifies positive `c` and `k`
before choosing any accuracy prescription or auction input. -/
def reciprocalThreshold (c k N : ℕ) : ℚ :=
  1 / ((c : ℚ) * ((N : ℚ) + 1) ^ k)

/-- Appendix A's decision language on the published canonical binary HDFPA codes.
Only normalized well-formed auctions are instances. Mathematical profiles remain real;
purity says each bidder chooses a single bid, and `IsNE` includes legality and the
bidder-dependent additive allowance `δ(|s|) * W_i`. Non-codes are outside the language. -/
def pureExistenceLanguage (δ : ℕ → ℚ) : CookPvsNP.Lang Bool :=
  {s | ∃ (n : ℕ) (H : HDFPA (Fin n)),
    decodeH s = some ⟨n, H⟩ ∧ H.WellFormed 1 ∧
    ∃ σ : H.Profile, H.Pure σ ∧ H.IsNE (δ s.length : ℝ) σ}

end CorrelatedAuctionComplexity.Main.Supplement


