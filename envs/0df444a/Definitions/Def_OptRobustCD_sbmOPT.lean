-- Prove2me | Definitions.Def_OptRobustCD_sbmOPT
-- name    : OptRobustCD_sbmOPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:58.01776+00:00
-- url     : https://prove2.me/theorems/cc6fef2c-518c-4367-9129-fec81b3c081f
-- title:
--   $\mathrm{OPT}_{d,\lambda}$ of p.1: the optimal asymptotic overlap of an estimator in SBM$(n,d,\lambda)$
-- statement:
--   The information-theoretically optimal overlap of p.1:
--   $$\mathrm{OPT}_{d,\lambda}=\lim_{n\to\infty}\ \sup_{\text{estimators }\hat\sigma}\ \frac1n\,\mathbb E_{(\sigma^\star,G)\sim\mathrm{SBM}(n,d,\lambda)}\bigl|\langle\sigma^\star,\hat\sigma(G)\rangle\bigr|.$$
--   Here an estimator maps a graph on $[n]$ to a labelling in $\{\pm1\}^n$, and $\frac1n|\langle\sigma^\star,\hat\sigma\rangle|$ is the overlap $\mathrm{ov}(\hat\sigma,\sigma^\star)$.
--
--   This is the benchmark of the main theorem (Theorem 1.1). Section 3.3 reuses the name for the tree quantity `OptRobustCD.treeOPT`; Theorem 3.7 relates the two.
--
--   **Formalization Note** The supremum is over deterministic estimators, a finite set; a randomized estimator's expected overlap is an average of deterministic ones. The limit is written $\limsup_{n}$, which equals the limit whenever it exists and is never smaller. The inner values lie in $[0,1]$ for $n\ge d(1+|\lambda|)$, so the real $\limsup$ is the true one.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §1 p.1 (pdf p.3)

import Mathlib
import Definitions.Def_OptRobustCD_Whp

namespace OptRobustCD

/-!
# OPT_{d,λ}, the optimal overlap in the block model (the definition on p.1)

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §1, p.1 (pdf p.3):

  OPT_{d,λ} = lim_{n→∞} sup_{estimators σ̂} (1/n) E_{(σ⋆,G)∼SBM(n,d,λ)} |⟨σ⋆, σ̂(G)⟩| .

**Formalization Note.**
* The supremum is over deterministic estimators `SimpleGraph (Fin n) → (Fin n → Bool)`, a finite
  type, so the real `⨆` is a maximum. A randomized estimator's expected overlap is an average of
  deterministic ones and does not exceed it.
* `lim_n` is written `limsup_n`, which equals the limit whenever it exists (the paper takes its
  existence for granted) and is never smaller. For `n ≥ d(1+|λ|)` the inner value lies in
  `[0, 1]`, so the sequence is eventually bounded and the real `limsup` is the true one.
* Theorem 1.1 compares with this `OPT`; §3.3 (p.14) reuses the name for the tree quantity
  `treeOPT` (Definition `OptRobustCD.treeOPT`), which Theorems 3.7 and 4.2 use.
-/

/-- `OPT_{d,λ}` of p.1: `limsup_n` of the best expected overlap of an estimator under SBM(n,d,λ). -/
noncomputable def sbmOPT (d lam : ℝ) : ℝ :=
  Filter.limsup (fun n : ℕ =>
    ⨆ f : SimpleGraph (Fin n) → (Fin n → Bool),
      SBMThreshold.Main.sbmExp n (sbmA d lam) (sbmB d lam)
        (fun σ G => SBMThreshold.Main.overlap σ (f G))) Filter.atTop

end OptRobustCD


