-- Prove2me | Definitions.Def_FairFacilityLoc_ratio
-- name    : FairFacilityLoc_ratio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:15.744657+00:00
-- url     : https://prove2.me/theorems/8a00d32a-92d9-481e-b7f5-421fddcfc660
-- title:
--   Definition 2.5: approximation ratio
-- statement:
--   The **approximation ratio** of a mechanism $M$ in dimension $d$ is
--   $$\rho_M(d)=\sup_{n,m,\mathcal G,x}\frac{F(M(x;\mathcal G);x,\mathcal G)}{\mathrm{OPT}(x,\mathcal G)},$$
--   over all numbers of agents and of groups, all group structures and all profiles, with the conventions $0/0=1$ and $a/0=\infty$ for $a>0$.
--
--   **Formalization Note** The value is in $[0,\infty]$ (`ℝ≥0∞`), and the two conventions are written out as cases of the ratio at one instance.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Definition 2.5, (2.2), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_FairFacilityLoc_objectiveF
import Definitions.Def_FairFacilityLoc_Mechanism

open scoped NNReal ENNReal

namespace FairFacilityLoc

/-- The **ratio at one instance** `F(M(x; G); x, G) / OPT(x, G)`, with the conventions `0/0 = 1` and
`a/0 = ∞` for `a > 0` (Yan, Zhou, manuscript, sha256 642a1268…, Definition 2.5, p.15, PDF p.17).

**Formalization Note.** Valued in `ℝ≥0∞`, with the two conventions written out. -/
noncomputable def ratioAt {n m d : ℕ} (M : Mechanism d) (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) :
    ℝ≥0∞ :=
  if optValue G x = 0 then
    (if objectiveF G x (M G x) = 0 then 1 else ⊤)
  else
    ((objectiveF G x (M G x) / optValue G x : ℝ≥0) : ℝ≥0∞)

/-- The **approximation ratio** `ρ_M(d)`, (2.2), p.15, PDF p.17: the supremum over all numbers `n` of agents
and `m` of groups, all group structures and all profiles. The supremum is in `ℝ≥0∞`. -/
noncomputable def ratio {d : ℕ} (M : Mechanism d) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (m : ℕ) (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d), ratioAt M G x

end FairFacilityLoc


