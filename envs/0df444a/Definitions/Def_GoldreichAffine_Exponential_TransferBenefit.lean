-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_TransferBenefit
-- name    : GoldreichAffine_Exponential_TransferBenefit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:27.044596+00:00
-- url     : https://prove2.me/theorems/67177a38-58f8-4556-bff2-2e585d8508b1
-- title:
--   Pairing law, transfer envelope and finite benefit optimization
-- statement:
--   For $w′\le n′$, $b′\le\min(b,n′)$ and $\ell=\min(w′,n′-w′)$, define the exact pairing weights
--   $$p_j=\frac{2^j\binom\ell j}{\binom{n′}{b′}}\sum_{h=0}^{\lfloor(b′-j)/2\rfloor}\binom{\ell-j}{h}\binom{n′-2\ell}{b′-j-2h}\quad(0\le j\le\min(b′,\ell)),$$
--   and $p_j=0$ for $\ell<j\le b′$. Set
--   $$\Phi(n′,w′,b′)=\sum_{j=0}^{b′}p_j\operatorname{adv}_j(M).$$
--   The advantage is always that of the original $b$-bit predicate $M$. For a feasible reduced guess, define
--   $$g=\log_2\frac{\binom n w}{\binom{n′}{w′}},\quad\eta_r=\log_2(1+2\Phi(n′,w′,b-r)),\quad v=\max_{0\le k_r\le\mu_r,\ \sum_rk_r\le n′}\sum_rk_r\eta_r.$$
--   Finally let $L=\min_{(n′,w′)\text{ feasible}}(g+n′-v)$. These definitions provide the precise quantities appearing in Lemmas 2 and 3. The assertion that $L$ lower-bounds the optimum is a separate theorem, never part of its definition.
--
--   **Formalization Note** The pairing sum includes both endpoints and the $j=0$ term. Its last binomial coefficient uses a signed lower index. Benefit and certificate extrema use extended real numbers; on the feasible source domain $0\le\Phi\le1/2$, $0\le\eta_r\le1$, $0\le v\le n′$, and all these extrema are finite and attained. Empty or unbounded real sets do not receive a default zero value. The unrestricted count function represents only its finite overlap coordinates.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 14 (PDF p. 15), Lemma 2 Eq. (9); Appendix A.2, Eqs. (12)–(13), p. 15 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_AttackModel
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- The exact pairing distribution in Lemma 2, including j=0 and ell=0. -/
noncomputable def pairingProbability (np wp bp j : ℕ) : ℝ :=
  let ell := min wp (np - wp)
  if j ≤ min bp ell then
    (2 : ℝ) ^ j * (ell.choose j : ℝ) / (np.choose bp : ℝ) *
      ∑ h ∈ Finset.range ((bp - j) / 2 + 1),
        ((ell - j).choose h : ℝ) *
          (binomZ (np - 2 * ell) ((bp : ℤ) - j - 2 * h) : ℝ)
  else 0

/-- Equation (9), always using the original predicate, including its empty residuals. -/
noncomputable def phi {b : ℕ} (M : Predicate b) (np wp bp : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (bp + 1), pairingProbability np wp bp j * advantage M j

noncomputable def guessingExponent (n w np wp : ℕ) : ℝ :=
  logTwo ((n.choose w : ℝ) / (np.choose wp : ℝ))

noncomputable def eta {b : ℕ} (M : Predicate b) (np wp r : ℕ) : ℝ :=
  logTwo (1 + 2 * phi M np wp (b - r))

/-- Equation (12): the exact continuous count-polytope maximum, as an extended sup.
    Valid inputs give 0 ≤ eta ≤ 1 and hence 0 ≤ benefit ≤ np, with attainment. -/
noncomputable def benefit {b : ℕ} (M : Predicate b) (n m np wp : ℕ) : EReal :=
  ⨆ (k : ℕ → ℝ) (_ : FeasibleCounts n m b np k),
    ((∑ r ∈ overlaps n b np, k r * eta M np wp r : ℝ) : EReal)

/-- The finite feasible-pair minimum in (13); no optimization certificate is built into C*. -/
noncomputable def lowerCertificate {b : ℕ} (M : Predicate b) (n m w : ℕ) : EReal :=
  ⨅ (np : ℕ) (wp : ℕ) (_ : FeasiblePair n w np wp),
    ((guessingExponent n w np wp + (np : ℝ) : ℝ) : EReal) - benefit M n m np wp

end GoldreichAffine.Exponential


