-- Prove2me | Definitions.Def_CPDETrial_IsCPDEAllocation
-- name    : CPDETrial_IsCPDEAllocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:58.751048+00:00
-- url     : https://prove2.me/theorems/1db62dcb-7082-440e-a0be-e78f00089fdf
-- title:
--   cPDE allocation over consideration sets $\mathcal M_t$
-- statement:
--   Given consideration sets $\mathcal M_t\subseteq\{1,\dots,M\}$, an allocation $(u^t)$ follows the cPDE rule if at every time $t$
--
--   $$
--   u^t\in\mathcal M_t\quad\text{and}\quad \nu^*_{u^t}(\mu^t,\Sigma^t)=\max_{j\in\mathcal M_t}\nu^*_j(\mu^t,\Sigma^t),
--   $$
--
--   with $\nu^*$ the cPDE index (EC.8) at the current posterior. With $\mathcal M_t=\{1,\dots,M\}$ this is the cPDE allocation policy of p. 11; smaller, possibly random, consideration sets are those allowed in §3.3. Ties may be broken by any rule (random tie-breaking is one).
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 11 (§3.2) and p. 12 (§3.3, M_t)

import Mathlib
import Definitions.Def_CPDETrial_nuStar
import Definitions.Def_CPDETrial_muT
import Definitions.Def_CPDETrial_SigT
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The cPDE allocation rule over consideration sets `M_t`.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §3.2, p. 11: "Our proposed cPDE allocation policy allocates one observation at time `t` to
the arm `i ∈ M` that maximizes `ν*_i(µ^t,Σ^t)`, with ties broken randomly"; §3.3, p. 12: "the
assumptions allow smaller subsets of arms, `M_t ⊆ M`, to be considered for allocation in any
given period `t`".

`IsCPDEAllocation mu0 Sig0 lam c θ ε u Mset` says: at every time `t` and outcome `ω`, the
allocated arm `u t ω` lies in the consideration set `Mset t ω` and maximizes the cPDE index
`ν*_j(µ^t(ω), Σ^t(ω))` (`nuStar`, eq. (EC.8)) over `j ∈ Mset t ω`, at the current posterior.

**Formalization Note.** Ties may be broken by any rule; together with `IsNonanticipating` the
rule may use the history and the external randomization (uniform random tie-breaking is one
instance). `Mset t ω` is nonempty because it contains `u t ω`. With `Mset t ω = univ` this is the
cPDE policy of p. 11 (App. B.10: "The allocation policies cPDE, … include all arms in every
`M_t`"). -/
def IsCPDEAllocation {M : ℕ} {Ω : Type*} (mu0 : Fin M → ℝ) (Sig0 : Matrix (Fin M) (Fin M) ℝ)
    (lam : Fin M → ℝ≥0) (c : Fin M → ℝ) (θ : Ω → EuclideanSpace ℝ (Fin M))
    (ε : ℕ → Fin M → Ω → ℝ) (u : ℕ → Ω → Fin M) (Mset : ℕ → Ω → Finset (Fin M)) : Prop :=
  ∀ t ω, u t ω ∈ Mset t ω ∧ ∀ j ∈ Mset t ω,
    nuStar c lam j (muT mu0 Sig0 lam θ ε u t ω) (SigT Sig0 lam u t ω) ≤
      nuStar c lam (u t ω) (muT mu0 Sig0 lam θ ε u t ω) (SigT Sig0 lam u t ω)

end CPDETrial


