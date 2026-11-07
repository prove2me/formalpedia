-- Prove2me | Definitions.Def_EffRobustLearn_weightVec
-- name    : EffRobustLearn_weightVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:16.688049+00:00
-- url     : https://prove2.me/theorems/d0eccfb9-a0ad-42c0-ab03-87067171dd9f
-- title:
--   The weights (3.8) and the weighted dataset
-- statement:
--   The weights of round $t$ are, on $(x,y)\in\bar S_{\mathrm{inp}}$,
--   $$w_t(x,y)=\frac{(|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|)y}{|\bar S_{\mathrm{inp}}|}\Big(\frac\alpha4\sum_{r=1}^{t-1}\frac{y(2+|\bar\mu_r(x)|)-\bar\mu_r(x)}{1+|\bar\mu_r(x)|}-(\bar\mu_t(x)-\bar\mu_1(x))\Big),$$
--   and on $x\in S_{\mathrm{ref}}$,
--   $$w_t(x,1)=\frac{|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|}{|S_{\mathrm{ref}}|}\Big(\frac\alpha2\sum_{r=1}^{t-1}\Big(\frac{\bar\mu_r(x)}{1+|\bar\mu_r(x)|}-h_r(x)\Big)-(\bar\mu_t(x)-\bar\mu_1(x))\Big).$$
--   The weighted dataset is the disjoint union $\bar S_{\mathrm{inp}}\cup\{(x,1):x\in S_{\mathrm{ref}}\}$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (3.8), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_muSeq

namespace EffRobustLearn

/-- The weights (3.8), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.15:
on `(x, y) ∈ S̄inp`, `w_t(x,y) = ((|S̄inp| + |Sref|) y / |S̄inp|) ((α/4) ∑_{r=1}^{t-1} (y(2 + |μ̄_r(x)|) - μ̄_r(x))/(1 + |μ̄_r(x)|) - (μ̄_t(x) - μ̄_1(x)))`, and
on `x ∈ Sref`, `w_t(x,1) = ((|S̄inp| + |Sref|)/|Sref|) ((α/2) ∑_{r=1}^{t-1} (μ̄_r(x)/(1 + |μ̄_r(x)|) - h_r(x)) - (μ̄_t(x) - μ̄_1(x)))`. -/
noncomputable def weightVec {X : Type*} {n m : ℕ} (ε : ℝ) (c0 : X → Bool) (c : ℕ → X → Bool)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (t : ℕ) : Fin n ⊕ Fin m → ℝ :=
  Sum.elim
    (fun i => (((n : ℝ) + m) * pm (Sinp i).2 / (n : ℝ)) *
      ((alphaStep (numRounds ε) / 4) * ∑ r ∈ Finset.Ico 1 t,
          (pm (Sinp i).2 * (2 + |muSeq c0 c r (Sinp i).1|) - muSeq c0 c r (Sinp i).1) /
            (1 + |muSeq c0 c r (Sinp i).1|)
        - (muSeq c0 c t (Sinp i).1 - muSeq c0 c 1 (Sinp i).1)))
    fun j => (((n : ℝ) + m) / (m : ℝ)) *
      ((alphaStep (numRounds ε) / 2) * ∑ r ∈ Finset.Ico 1 t,
          (muSeq c0 c r (Sref j) / (1 + |muSeq c0 c r (Sref j)|) - hSeq ε c0 c r (Sref j))
        - (muSeq c0 c t (Sref j) - muSeq c0 c 1 (Sref j)))

/-- The disjoint union `S̄inp ∪ {(x, 1) : x ∈ Sref}` of Algorithm 1, line 7, p.14. -/
def weightedData {X : Type*} {n m : ℕ} (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    Fin n ⊕ Fin m → X × Bool :=
  Sum.elim Sinp fun j => (Sref j, true)

end EffRobustLearn


