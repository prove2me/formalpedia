-- Prove2me | Definitions.Def_NearOptOWF_KeyedFam_IsSubexpPRF
-- name    : NearOptOWF_KeyedFam_IsSubexpPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:07.729938+00:00
-- url     : https://prove2.me/theorems/2d1739a7-6e00-44f5-8a6f-3d8d07700895
-- title:
--   Sub-exponentially secure PRF (oracle indistinguishability)
-- statement:
--   A keyed family $K$ is a **sub-exponentially secure PRF** if there is $\delta > 0$ such that for every polynomial $p$, all sufficiently large $\lambda$, all $n, m \le p(\lambda)$ and every adaptive oracle distinguisher $D$ of size at most $p(\lambda)$,
--   $$
--   \Bigl|\Pr_k\bigl[D^{f_k} = 1\bigr] - \Pr_{R}\bigl[D^{R} = 1\bigr]\Bigr| \le 2^{-\lambda^\delta},
--   $$
--   where $R$ is a uniformly random function $\{0,1\}^n \to \{0,1\}^m$.
--
--   It is the hypothesis of Lemma 4.10. No efficiency of $K$ is part of this predicate.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19); §3, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_KeyedFam
import Definitions.Def_NearOptOWF_OracleDist_size
import Definitions.Def_NearOptOWF_OracleDist_run
import Definitions.Def_LaconicBarrier_coinAvg

namespace NearOptOWF

open LaconicBarrier

/-- `K` is a **sub-exponentially secure PRF** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Lemma 4.10, p.17 (PDF p.19); "sub-exponentially
secure", §3, p.8 (PDF p.10)): there is `δ > 0` such that for every polynomial `p`, for all
sufficiently large `λ`, all `n, m ≤ p(λ)` and every adaptive oracle distinguisher `D` of size at most
`p(λ)`, the probability that `D` outputs `1` with oracle `f_k` (`k` a uniform key) and with oracle a
uniformly random function `R : {0,1}ⁿ → {0,1}ᵐ` differ by at most `2^{−λ^δ}`.

**Formalization Note** Distinguishers are non-uniform (`OracleDist`). No efficiency of `K` is
required here; the puncturable PRFs of the mission carry their own efficiency clause
(`PPRF.IsSubexpPPRF`). -/
def KeyedFam.IsSubexpPRF (K : KeyedFam) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ p : Polynomial ℕ, ∀ᶠ lam : ℕ in Filter.atTop,
    ∀ n m : ℕ, n ≤ p.eval lam → m ≤ p.eval lam → ∀ D : OracleDist, D.size ≤ p.eval lam →
      |coinAvg (K.keyLen lam n m) (fun key =>
          if D.run n (K.circ lam n m key).eval = true then 1 else 0) -
        (∑ R : (Fin n → Bool) → (Fin m → Bool),
            (if D.run n (fun q => List.ofFn (R (fun i => q.getD (i : ℕ) false))) = true
              then 1 else 0 : ℝ)) /
          (Fintype.card ((Fin n → Bool) → (Fin m → Bool)) : ℝ)| ≤
        (2 : ℝ) ^ (-(lam : ℝ) ^ δ)

end NearOptOWF


