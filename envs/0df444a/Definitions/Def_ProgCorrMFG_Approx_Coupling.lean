-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_Coupling
-- name    : ProgCorrMFG_Approx_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:24.995162+00:00
-- url     : https://prove2.me/theorems/8055dcf3-5031-4cd3-8041-abc021c1adc1
-- title:
--   §6, (6.15)–(6.19), pp. 20–21 — the coupling of the proof of (6.3): $X^{j,N}$, $\tilde X^{j,N}$, $\hat X^{j,N}$, $\bar X^{1,N}$
-- statement:
--   This file defines the coupled processes that the paper constructs on one probability space in the proof of (6.3).
--
--   **Primitive variables.** On a probability space there are: initial states $X^j_0$, $j=1,\dots,N$, i.i.d. $\mathfrak m_0$; seeds $Z_1,\dots,Z_N$ i.i.d. $\nu$; a flow $\mu\sim\rho_2$; noises $\xi^j_t$ i.i.d. $\nu$; and coins $\vartheta_t$ i.i.d. $\nu$; the families $\xi$, $(X^j_0)_j$, $(\mu,(Z_j)_j)$ and $\vartheta$ are independent, and $Z$ is independent of $\mu$. With the maps $\alpha_t$ of (R2), the suggestions are $\Phi_j(t,\cdot)=\alpha_t(Z_j,\mu^{(t+1)})$. Player 1 deviates with $\tilde\Upsilon_1(t,\cdot)=w_t(\vartheta_t,\Phi_1)$ for Borel maps $w_t:[0,1]\times\mathcal R\to\widehat{\mathcal E}_{t,N}$.
--
--   **Processes.** Almost surely, for $t\in[\![0,T-1]\!]$:
--   1. (6.16) every player follows the suggestion: $X^{j,N}_{t+1}=\Psi(t,X^{j,N}_t,\mu^{j,N}_t,\Phi_j(t,X^{j,N}_t),\xi^j_{t+1})$, with $\mu^{j,N}$ the empirical measure of the others;
--   2. (6.17) only player 1 deviates: $\tilde X^{1,N}_{t+1}=\Psi(t,\tilde X^{1,N}_t,\tilde\mu^{1,N}_t,\tilde\Upsilon_1(t,\tilde X^{1,N},\tilde\mu^{1,N}),\xi^1_{t+1})$ and $\tilde X^{j,N}_{t+1}=\Psi(t,\tilde X^{j,N}_t,\tilde\mu^{j,N}_t,\Phi_j(t,\tilde X^{j,N}_t),\xi^j_{t+1})$ for $j\ge2$;
--   3. (6.18) players $2,\dots,N$ only: $\hat X^{j,N}_{t+1}=\Psi(t,\hat X^{j,N}_t,\hat\mu^{1,N}_t,\Phi_j(t,\hat X^{j,N}_t),\xi^j_{t+1})$ with $\hat\mu^{1,N}_t=\frac1{N-1}\sum_{k=2}^N\delta_{\hat X^{k,N}_t}$;
--   4. (6.19) the auxiliary process $\bar X^{1,N}_{t+1}=\Psi(t,\bar X^{1,N}_t,\mu_t,\tilde u^{1,N}_t,\xi^1_{t+1})$ with $\tilde u^{1,N}_t=\tilde\Upsilon_1(t,\tilde X^{1,N},\tilde\mu^{1,N})$;
--
--   all started from $X^j_0$.
--
--   **Formalization Note** Player $j$ is index $j-1$; the noise $\xi^j_{t+1}$ is `noise ω t (j-1)`. The deviation is given by the maps $w_t$ directly (the Doob-lemma form of Definition 3.1 v), footnote 1 on p. 20). The value of `sth ω t 0` is unconstrained and never used.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, pp. 20–21, (6.15)–(6.19) and footnote 1

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval

/-- The coupling of the proof of (6.3) (pp. 20–21), for `N` players, a flow law `ρ₂` and the maps
`α_t` of (R2), on a probability space `(Ω, P)`.

Primitive variables (i)–(iv), encoded in `law`: initial states `X^j_0` i.i.d. `𝔪₀` (`init`), seeds
`Z_j` i.i.d. `ν` (`seed`), the flow `μ ∼ ρ₂` (`flow`), noises `ξ^j_{t+1}` i.i.d. `ν` (`noise ω t j`)
and coins `ϑ_t` i.i.d. `ν` (`coin`), with `ξ`, `X_0`, `(μ, Z)` and `ϑ` independent and `Z`
independent of `μ`. The suggestions are `Φ_j(t, ·) := α_t(Z_j, μ^{(t+1)})`. Player 1 (index `0`)
deviates with `Υ̃_1(t, ·) := w_t(ϑ_t, Φ_1)`, `w_t : [0,1] × ℛ → ℰ̂_{t,N}` Borel (v)).

Processes, each defined by its recursion almost surely:
* `X^{j,N}` (`st`), (6.16): every player follows the suggestion, driven by `μ^{j,N}`;
* `X̃^{j,N}` (`stt`), (6.17): player 1 plays `Υ̃_1`, the others follow, driven by `μ̃^{j,N}`;
* `X̂^{j,N}`, `j ∈ ⟦2, N⟧` (`sth`), (6.18): players `2, …, N` only, all driven by
  `μ̂^{1,N} = (N−1)⁻¹ ∑_{k=2}^N δ_{X̂^{k,N}}` (the value `sth ω t 0` plays no role);
* `X̄^{1,N}` (`stb`), (6.19): driven by the true flow `μ_t` and player 1's deviating controls
  `ũ^{1,N}_t = Υ̃_1(t, X̃^{1,N}, μ̃^{1,N})`. -/
structure Coupling {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [MeasurableSpace X]
    [MeasurableSpace G] (M : Model T X G) (m₀ : Measure X) (ρ₂ : Measure (Flow T X))
    (α : (t : Fin T) → I → (Fin (t.1 + 2) → Meas X) → (X → G)) (N : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) where
  init : Ω → Fin N → X
  seed : Ω → Fin N → I
  flow : Ω → Flow T X
  noise : Ω → Fin T → Fin N → I
  coin : Ω → Fin T → I
  wdev : (t : Fin T) → I → Strat T X G → CompN T X G (N - 1) t
  st : Ω → Fin (T + 1) → Fin N → X
  stt : Ω → Fin (T + 1) → Fin N → X
  sth : Ω → Fin (T + 1) → Fin N → X
  stb : Ω → Fin (T + 1) → X
  measurable_init : Measurable init
  measurable_seed : Measurable seed
  measurable_flow : Measurable flow
  measurable_noise : Measurable noise
  measurable_coin : Measurable coin
  measurable_wdev : ∀ t, Measurable (fun p : I × Strat T X G => wdev t p.1 p.2)
  measurable_st : Measurable st
  measurable_stt : Measurable stt
  measurable_sth : Measurable sth
  measurable_stb : Measurable stb
  law : P.map (fun ω => (noise ω, init ω, (flow ω, seed ω), coin ω)) =
    (Measure.pi fun _ : Fin T => Measure.pi fun _ : Fin N => (volume : Measure I)).prod
      ((Measure.pi fun _ : Fin N => m₀).prod
        ((ρ₂.prod (Measure.pi fun _ : Fin N => (volume : Measure I))).prod
          (Measure.pi fun _ : Fin T => (volume : Measure I))))
  dyn_st : ∀ᵐ ω ∂P, st ω 0 = init ω ∧ ∀ (t : Fin T) (j : Fin N),
    st ω t.succ j = M.Ψ t (st ω t.castSucc j) (empOthers (st ω t.castSucc) j).1
      (α t (seed ω j) (histSucc (flow ω) t) (st ω t.castSucc j)) (noise ω t j)
  dyn_stt : ∀ᵐ ω ∂P, stt ω 0 = init ω ∧ ∀ (t : Fin T) (j : Fin N),
    stt ω t.succ j = M.Ψ t (stt ω t.castSucc j) (empOthers (stt ω t.castSucc) j).1
      (if j = ⟨0, by have := j.2; omega⟩ then
        (wdev t (coin ω t) (fun s => α s (seed ω j) (histSucc (flow ω) s))).1
          (fun s => stt ω s j) (fun s => empOthers (stt ω s) j)
      else α t (seed ω j) (histSucc (flow ω) t) (stt ω t.castSucc j)) (noise ω t j)
  dyn_sth : ∀ᵐ ω ∂P, ∀ j : Fin N, j.1 ≠ 0 → sth ω 0 j = init ω j ∧ ∀ t : Fin T,
    sth ω t.succ j = M.Ψ t (sth ω t.castSucc j)
      (empOthers (sth ω t.castSucc) ⟨0, by have := j.2; omega⟩).1
      (α t (seed ω j) (histSucc (flow ω) t) (sth ω t.castSucc j)) (noise ω t j)
  dyn_stb : ∀ᵐ ω ∂P, ∀ h : 0 < N, stb ω 0 = init ω ⟨0, h⟩ ∧ ∀ t : Fin T,
    stb ω t.succ = M.Ψ t (stb ω t.castSucc) (flow ω t.castSucc)
      ((wdev t (coin ω t) (fun s => α s (seed ω ⟨0, h⟩) (histSucc (flow ω) s))).1
        (fun s => stt ω s ⟨0, h⟩) (fun s => empOthers (stt ω s) ⟨0, h⟩))
      (noise ω t ⟨0, h⟩)

end ProgCorrMFG.Approx


