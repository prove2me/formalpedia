-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_Model
-- name    : GainShareOpt_StochBalance_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:46:53.518319+00:00
-- url     : https://prove2.me/theorems/1ac4320b-d4b3-494c-9df2-2087f71c7259
-- title:
--   OM-SR instances, the Stochastic Balance run ST-BA(f) and the dual updates (43) (App. B.1)
-- statement:
--   An **OM-SR instance** consists of offline agents $U=\{0,\dots,m-1\}$, online agents $V=\{0,\dots,n-1\}$ listed in their arrival order, a neighbourhood $N_v\subseteq U$ for each arrival $v$, and weights $w_u>0$ (unit capacities); at least one edge is present. The online neighbours of $u$ are $N_u=\{v: u\in N_v\}$.
--
--   Fix a gain-sharing function $f$ and a common success probability $p$. The **Stochastic Balance** run ST-BA$(f)$ processes the arrivals in order. The load of $u$ is $\ell_u=p\cdot(\text{number of earlier arrivals assigned to }u)$, and $u$ is *available* while none of its assignments has succeeded. Arrival $v$ is assigned to an available neighbour maximizing
--   $$w_u\,p\,\bigl(1-f(\ell_u)\bigr),$$
--   ties broken towards the least index; if no neighbour is available, $v$ stays unassigned. The assignment succeeds with probability $p$, independently (coin $\omega_v$); success makes $u$ unavailable. All duals start at $0$, and when $v$ is assigned to $u$ with pre-assignment load $\ell_u$, (43) sets
--   $$\alpha_u\leftarrow\alpha_u+w_u\,p\,f(\ell_u),\qquad \beta_v\leftarrow w_u\,p\,\bigl(1-f(\ell_u)\bigr),$$
--   whether or not the assignment succeeds; an unassigned $v$ keeps $\beta_v=0$. The expectation over outcomes is the finite sum over $\omega\in\{0,1\}^V$ with weight $\prod_v p^{\omega_v}(1-p)^{1-\omega_v}$.
--
--   These objects are the discrete model on which the certificate functional (44) is defined.
--
--   **Formalization Note** `choice` picks the least index among the available maximizers (`Fin.find`); `finalState` folds `step` over the arrivals; `expect` is the weighted finite sum.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), pp. 21–22, App. B.1 and (43)

import Mathlib

open Classical

namespace GainShareOpt.StochBalance

/-- A finite instance of vertex-weighted online matching with stochastic rewards (OM-SR),
Appendix B.1 of Xu (arXiv:2503.09508). Offline agents are `Fin m`; online agents are `Fin n`,
listed in their (adversarial, outcome-independent) arrival order; `nbr v` is the neighbourhood
`N_v` revealed when `v` arrives; `w u > 0` is the weight of offline agent `u` (unit capacity).
The certificate functional (44) ranges over instances with at least one edge. -/
structure Instance where
  m : ℕ
  n : ℕ
  nbr : Fin n → Finset (Fin m)
  w : Fin m → ℝ
  w_pos : ∀ u, 0 < w u
  has_edge : ∃ v, (nbr v).Nonempty

/-- The online neighbours `N_u = {v : u ∈ N_v}` of an offline agent `u`. -/
def Instance.onlineNbrs (I : Instance) (u : Fin I.m) : Finset (Fin I.n) :=
  Finset.univ.filter (fun v => u ∈ I.nbr v)

/-- The state of a Stochastic Balance run after some prefix of the arrivals: the number of
assignments made to each offline agent (its load is `p` times this count), whether each offline
agent is still available (no assignment to it has succeeded), and the dual variables
`α_u`, `β_v`. -/
structure RunState (m n : ℕ) where
  cnt : Fin m → ℕ
  avail : Fin m → Bool
  alpha : Fin m → ℝ
  beta : Fin n → ℝ

/-- The initial state: no loads, every offline agent available, all duals zero. -/
def RunState.init (m n : ℕ) : RunState m n :=
  ⟨fun _ => 0, fun _ => true, fun _ => 0, fun _ => 0⟩

/-- The ST-BA(f) choice for arrival `v` with common success probability `p`: among the available
neighbours, an agent maximizing the score `w_u p (1 - f(ℓ_u))` with `ℓ_u = p · cnt u` the
pre-assignment load; ties go to the least index. `none` when no neighbour is available. -/
noncomputable def choice (I : Instance) (f : ℝ → ℝ) (p : ℝ) (st : RunState I.m I.n)
    (v : Fin I.n) : Option (Fin I.m) :=
  let A := (I.nbr v).filter (fun u => st.avail u = true)
  let score : Fin I.m → ℝ := fun u => I.w u * p * (1 - f (p * (st.cnt u : ℝ)))
  let P : Fin I.m → Prop := fun u => u ∈ A ∧ ∀ u' ∈ A, score u' ≤ score u
  if h : ∃ u, P u then some (Fin.find P h) else none

/-- One step of ST-BA(f) with the dual updates (43): if arrival `v` is assigned to `u` with
pre-assignment load `ℓ_u`, then `α_u ← α_u + w_u p f(ℓ_u)`, `β_v ← w_u p (1 - f(ℓ_u))`, the load of
`u` grows by `p`, and `u` becomes unavailable iff the assignment succeeds (`ω v = true`).
An unassigned arrival changes nothing (so `β_v` stays `0`). -/
noncomputable def step (I : Instance) (f : ℝ → ℝ) (p : ℝ) (ω : Fin I.n → Bool)
    (st : RunState I.m I.n) (v : Fin I.n) : RunState I.m I.n :=
  match choice I f p st v with
  | none => st
  | some u =>
    { cnt := Function.update st.cnt u (st.cnt u + 1)
      avail := Function.update st.avail u (st.avail u && !ω v)
      alpha := Function.update st.alpha u (st.alpha u + I.w u * p * f (p * (st.cnt u : ℝ)))
      beta := Function.update st.beta v (I.w u * p * (1 - f (p * (st.cnt u : ℝ)))) }

/-- The final state of ST-BA(f) on instance `I` under success outcomes `ω` (one coin per
arrival; the coin of `v` decides the assignment of `v` if there is one). -/
noncomputable def finalState (I : Instance) (f : ℝ → ℝ) (p : ℝ) (ω : Fin I.n → Bool) :
    RunState I.m I.n :=
  (List.finRange I.n).foldl (step I f p ω) (RunState.init I.m I.n)

/-- The probability of the outcome vector `ω` when the coins are independent Bernoulli(`p`). -/
noncomputable def coinWeight {n : ℕ} (p : ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ v, if ω v then p else 1 - p

/-- Expectation over the assignment outcomes, as a finite weighted sum. -/
noncomputable def expect (I : Instance) (p : ℝ) (X : (Fin I.n → Bool) → ℝ) : ℝ :=
  ∑ ω : Fin I.n → Bool, coinWeight p ω * X ω

end GainShareOpt.StochBalance


