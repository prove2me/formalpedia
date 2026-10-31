-- Prove2me | Definitions.Def_FairExplore_Welfare
-- name    : FairExplore_Welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:02.660763+00:00
-- url     : https://prove2.me/theorems/a81d028b-b103-4971-9165-dac7c39ab09d
-- title:
--   Utility gain $\mathrm{UtilGain}^g$ and Nash social welfare $SW(\pi,\mathcal I)$
-- statement:
--   The fairness criterion of §2.3.
--
--   1. **Disagreement point.** $\tilde R^g_T(\mathcal I)=R_T(\pi^*_g,\mathcal I_g)$, the regret of the KL-UCB policy on the single-group instance $\mathcal I_g$.
--   2. **Utility gain** (3):
--   $$\mathrm{UtilGain}^g(\pi,\mathcal I)=\liminf_{T\to\infty}\frac{\tilde R^g_T(\mathcal I)-R^g_T(\pi,\mathcal I)}{\log T}.$$
--   3. **Nash social welfare** (4):
--   $$SW(\pi,\mathcal I)=\sum_{g\in G}\log\big(\mathrm{UtilGain}^g(\pi,\mathcal I)\big),\qquad \log u\triangleq-\infty\ \text{for}\ u\le0.$$
--
--   A policy is unfair when some group gains nothing over learning alone ($SW=-\infty$); Theorem 3 says PF-UCB attains $SW=Y^*(\mathcal I)$.
--
--   **Formalization Note** The liminf is taken in `EReal` (so it may be $\pm\infty$), as are the logarithm and the sum; $\log(+\infty)=+\infty$ is a convention that the policies considered never reach. The KL-UCB policy of the disagreement point breaks ties with its own rule `selD`, a parameter.
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, §2.3, p.8 ((2), (3)); (4), p.9; Proposition 1, p.9

import Mathlib
import Definitions.Def_FairExplore_Policies

open Filter

namespace FairExplore

variable {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DecidableEq γ] [DecidableEq α]

/-- The disagreement-point regret `R̃^g_T(I) = R_T(π*_g, I_g)` (§2.3, p.8), with `π*_g` the KL-UCB
policy on the single-group instance `I_g` (Proposition 1, p.9), whose ties are broken by `selD`. -/
noncomputable def Rtilde (S : GroupedStructure γ α) (θ : α → ℝ)
    (selD : Finset (Option α) → Option α) (g : γ) (T : ℕ) : ℝ :=
  regretNull S θ g (klucb (single S g).A selD) T

/-- The asymptotic utility gain (3) (p.8):
`UtilGain^g(π, I) = liminf_{T → ∞} (R̃^g_T(I) − R^g_T(π, I)) / log T`, in `EReal`.

**Formalization Note** The liminf of the real sequence is taken in `EReal`, so it is `±∞` when the
sequence is unbounded; the term at `T ∈ {0, 1}` (where `log T = 0`) does not affect it. -/
noncomputable def utilGain (S : GroupedStructure γ α) (θ : α → ℝ)
    (selD : Finset (Option α) → Option α) (π : Policy γ α) (g : γ) : EReal :=
  liminf (fun T : ℕ => (((Rtilde S θ selD g T - groupRegretK S θ π T g) / Real.log T : ℝ) : EReal))
    atTop

/-- `log u` on `EReal` with the paper's convention `log u ≜ −∞` for `u ≤ 0` ((4), p.9).

**Formalization Note** `log ⊤ = ⊤`; a utility gain is never `⊤` for the policies considered. -/
noncomputable def elogE (u : EReal) : EReal :=
  if u ≤ 0 then ⊥ else if u = ⊤ then ⊤ else ((Real.log u.toReal : ℝ) : EReal)

/-- The Nash social welfare (4) (p.9): `SW(π, I) = ∑_{g ∈ G} log(UtilGain^g(π, I))`, with
`log u = −∞` for `u ≤ 0`, in `EReal`. -/
noncomputable def SW (S : GroupedStructure γ α) (θ : α → ℝ)
    (selD : Finset (Option α) → Option α) (π : Policy γ α) : EReal :=
  ∑ g, elogE (utilGain S θ selD π g)

end FairExplore


