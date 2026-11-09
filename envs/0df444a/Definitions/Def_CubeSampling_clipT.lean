-- Prove2me | Definitions.Def_CubeSampling_clipT
-- name    : CubeSampling_clipT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:18.519207+00:00
-- url     : https://prove2.me/theorems/e633ed06-ef3a-479d-976f-14d59c180687
-- title:
--   $T_{d,k}(\eta) = \sup_{h \in P_{d,k},\,\mathbb E[h^2]=1} b_\eta(h)$
-- statement:
--   $$
--   T_{d,k}(\eta) = \sup_{h \in P_{d,k},\ \mathbb E[h^2] = 1} b_\eta(h),
--   $$
--   the smallest clipping level that preserves at least $\eta$ energy for every unit polynomial of degree at most $k$.
--
--   **Formalization Note** For $0 < \eta < 1$ the set is nonempty ($h = 1$) and bounded above by $2^d$, so the real supremum agrees with the paper's.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 2.2, p.8

import Mathlib
import Definitions.Def_CubeSampling_clipLevel
import Definitions.Def_CubeSampling_lowDeg

namespace CubeSampling

/-- `T_{d,k}(η) = sup_{h ∈ P_{d,k}, E[h²] = 1} b_η(h)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §2.2, p.8), the smallest clipping level
that preserves at least `η` energy for every unit polynomial of degree at most `k`.

**Formalization Note** For `0 < η < 1` the set is nonempty (`h = 1`) and bounded above by `2^d`
(sanity file), so the real supremum is the paper's. -/
noncomputable def clipT (d k : ℕ) (η : ℝ) : ℝ :=
  sSup {b : ℝ | ∃ h ∈ lowDeg d k, cubeMean d (fun x => h x ^ 2) = 1 ∧ clipLevel d η h = b}

end CubeSampling


