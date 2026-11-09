-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Analysis
-- name    : OnlineSteinitz_Reduction_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:05.839651+00:00
-- url     : https://prove2.me/theorems/5ca353fe-e27a-47b3-be42-5969025df633
-- title:
--   Residuals, split errors and centered signing quantities
-- statement:
--   For a completed output $w_0,\ldots,w_{T-1}$, define its arbitrary-total proportional residual and maximum residual by
--   $$\operatorname{res}_k=\sum_{j<k}w_j-\frac{k}{T}\sum_{j<T}w_j,\qquad
--   \operatorname{res}_{\max}=\max_{0\le k\le T}\|\operatorname{res}_k\|.$$
--   For a tree interval $I_u$, define $\operatorname{tot}_u=\sum_{j\in I_u}w_j$ and $\operatorname{err}_u=\operatorname{tot}_{u_L}-(m_{u_L}/m_u)\operatorname{tot}_u$. For local visit records, set $\mu=m^{-1}\sum_i x_i$, $Y=\sum_i\varepsilon_i(x_i-\mu)$ and $R=\operatorname{err}-Y/2$, where the local error uses the actual destinations.
--
--   The terminal success predicate is precisely $\|S\|\le V(m)$ and $|q|\le W(m)$. The simultaneous prefix predicate uses the exact budget
--   $$\sum_{u\in P(k)}\left((V(m_u)+W(m_u))/2+\mathbf1_{\{m_u\text{ odd}\}}\right).$$
--   The centered path sum is $\frac12\sum_{u\in P(k)}\alpha_{u,k}Y_u$ and the count path sum is $\sum_{u\in P(k)}\alpha_{u,k}|q_u|$. These definitions share the actual router records; none includes an asserted bound. The maximum is over the nonempty finite set of all $T+1$ prefixes. All scalar quotients use real division.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, (2.1), p.4; (2.3), p.6; (2.5)–(2.6), p.7; Lemma 2.3 and definition of R, pp.8–9; (2.11)–(2.12), p.10

import Definitions.Def_OnlineSteinitz_Reduction_Router

open scoped BigOperators

namespace OnlineSteinitz.Reduction

/-! (2.1), (2.5)–(2.6), pp.4,7; local quantities of Lemma 2.3, pp.8–9. -/
noncomputable def residual {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : ℕ) (w : ℕ → E) (k : ℕ) : E :=
  (∑ j ∈ Finset.range k, w j) - ((k : ℝ) / T) • ∑ j ∈ Finset.range T, w j

noncomputable def intervalTotal {E : Type*} [AddCommGroup E]
    (w : ℕ → E) (a m : ℕ) : E := ∑ j ∈ Finset.range m, w (a + j)

noncomputable def splitError {T : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ℕ → E) (u : Node T) : E :=
  intervalTotal w u.1.val (leftSize u.2.val) -
    ((leftSize u.2.val : ℝ) / u.2.val) • intervalTotal w u.1.val u.2.val

noncomputable def localMean {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : List (Visit E)) : E :=
  (1 / (h.length : ℝ)) • (h.map Visit.vector).sum

noncomputable def centeredSum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : List (Visit E)) : E :=
  (h.map (fun e => sign e.proposed • (e.vector - localMean h))).sum

noncomputable def localError {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (h : List (Visit E)) : E :=
  ((h.filter Visit.actual).map Visit.vector).sum -
    ((leftSize m : ℝ) / m) • (h.map Visit.vector).sum

noncomputable def remainder {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (h : List (Visit E)) : E := localError m h - (1 / 2 : ℝ) • centeredSum h

noncomputable def terminalGood {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V W : ℕ → ℝ) (m : ℕ) (h : ProposalHistory E) : Prop :=
  ‖signedVector h‖ ≤ V m ∧ |signedCount h| ≤ W m

noncomputable def prefixBudget (T : ℕ) (V W : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ u ∈ boundaryPath T k,
    ((V u.2.val + W u.2.val) / 2 + if Odd u.2.val then 1 else 0)

noncomputable def prefixGood {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (V W : ℕ → ℝ) (r : Run T E) : Prop :=
  ∀ k : ℕ, k ≤ T → ‖residual T (output r) k‖ ≤ prefixBudget T V W k

noncomputable def maxResidual {T : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : Run T E) : ℝ :=
  (Finset.range (T + 1)).sup' (by simp) (fun k => ‖residual T (output r) k‖)

noncomputable def centeredPath {T : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : Run T E) (k : ℕ) : E :=
  (1 / 2 : ℝ) • ∑ u ∈ boundaryPath T k, alpha u k • centeredSum (r.localHistory u)

noncomputable def countPath {T : ℕ} {E : Type*} (r : Run T E) (k : ℕ) : ℝ :=
  ∑ u ∈ boundaryPath T k, alpha u k * |signedCount (proposedHistory (r.localHistory u))|

end OnlineSteinitz.Reduction


