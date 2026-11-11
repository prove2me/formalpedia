-- Prove2me | Definitions.Def_AgnGaussTomo_optG
-- name    : AgnGaussTomo_optG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:38.738976+00:00
-- url     : https://prove2.me/theorems/e0dba86b-25b7-4408-ab50-b548bd965e77
-- title:
--   Best Gaussian infidelity $\mathrm{opt}=1-\sup_{\psi\in\mathcal G}\langle\psi|\rho|\psi\rangle$
-- statement:
--   Let $\mathcal G$ be the set of pure Gaussian states of $n$ modes. For a state $\rho$,
--
--   $$
--   \mathrm{opt}(\rho)=1-\sup_{|\psi\rangle\in\mathcal G}\langle\psi|\rho|\psi\rangle=\inf_{|\psi\rangle\in\mathcal G}d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)
--   $$
--
--   is the smallest infidelity to $\rho$ achievable by a pure Gaussian state (Eq. (1)). It is the benchmark of agnostic tomography: a learner is asked to output a Gaussian state that is nearly as good as the best one.
--
--   **Formalization Note** $\mathcal G$ is the published `OptGaussTomo.bosePure n` (pure Gaussian states of any energy). The infimum is the real infimum over this set, which is non-empty (it contains the vacuum) and on which the infidelity is bounded below by $0$.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §1, Eq. (1), printed p. 1 (PDF p. 4); Proposition 3.15, p. 24 (PDF p. 27)

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_AgnGaussTomo_infid

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **The best Gaussian infidelity `opt = 1 − sup_{|ψ⟩∈G} ⟨ψ|ρ|ψ⟩`.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §1,
Eq. (1), printed p. 1 (PDF p. 4): "if we let G denote the set of pure Gaussian states, for a given
state ρ, we can let opt = 1 − sup_{|ψ⟩∈G} ⟨ψ| ρ |ψ⟩ (1)"; equivalently (Proposition 3.15, p. 24)
"opt = inf_{|ψ⟩∈G} d_IF(ρ, |ψ⟩⟨ψ|)".

**Formalization Note.** `G` is the published `OptGaussTomo.bosePure n` (pure Gaussian states,
no energy bound). The real infimum is over the subtype `bosePure n`, which is non-empty (it
contains the vacuum) and on which `infid ρ ·` is bounded below by `0` for a density `ρ`
(`tr(ρ|ψ⟩⟨ψ|) ≤ 1`), so the real `⨅` is the true infimum and never the junk value of an empty or
unbounded index set. -/
noncomputable def optG {n : ℕ} (ρ : State (Occupation (Fin n))) : ℝ :=
  ⨅ σ : OptGaussTomo.bosePure n, infid ρ.coefficients σ.1.coefficients

end AgnGaussTomo


