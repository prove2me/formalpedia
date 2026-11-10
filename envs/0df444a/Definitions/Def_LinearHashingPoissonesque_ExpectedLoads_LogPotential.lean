-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
-- name    : LinearHashingPoissonesque_ExpectedLoads_LogPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:09.498951+00:00
-- url     : https://prove2.me/theorems/0ed7319a-151e-4b8e-8524-d5cd74b7517b
-- title:
--   Centered log-average-exponential potential
-- statement:
--   Let $S\subseteq A$ be finite, let $f:A\to B$ hash it into a nonempty finite set of $n$ bins, and put $\mu=|S|/n$. For every real parameter $\lambda$, define
--
--   $$\phi_\lambda(S,f)=\log\!\left(\frac1n\sum_{y\in B}\exp(\lambda(L_y(S,f)-\mu))\right).$$
--
--   The center is computed from $S$ and the full bin set. Each exponential is positive, so the logarithm has a positive argument. The same potential is used for arbitrary functions in Lemma 3 and for uniformly random linear maps in Theorem 7.
--
--   **Formalization Note** The formula is total on any finite type of bins; only nonempty binary coordinate spaces occur in the mission. There are no measure-theoretic integrability defaults because this is a finite sum.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.10, Section 3, potential definition; p.3, Eq.(1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 3, p.10: log of the average of exponentials of the centered loads.
All bins are counted and the center is always |S| divided by the number of bins. -/
noncomputable def logPotential {A B : Type*} [Fintype B]
    (S : Finset A) (f : A → B) (lam : ℝ) : ℝ :=
  Real.log ((∑ y : B, Real.exp (lam * ((binLoad S f y : ℝ) -
    (S.card : ℝ) / (Fintype.card B : ℝ)))) / (Fintype.card B : ℝ))

end LinearHashingPoissonesque.ExpectedLoads


