-- Prove2me | Definitions.Def_FakeUserRanking_FORC_GoodEvent
-- name    : FakeUserRanking_FORC_GoodEvent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:39.718964+00:00
-- url     : https://prove2.me/theorems/8a89d0a4-6f84-4442-8976-38772570c093
-- title:
--   Definition 1, pp. 28–29 — level exposure, the windows (21), the events G^(ℓ)_{i,t} (22), G₁, G₂, G, and γ_{j,i} (23)
-- statement:
--   This file defines the good event of the proof of Theorem 3 and the sample thresholds $\gamma_{j,i}$.
--
--   Write $\eta^{(\ell)}_{i,t},\hat\eta^{(\ell)}_{i,t},\hat r^{(\ell)}_{i,t}$ for FORC's quantities at the end of round $t$ (after Steps 8–11). Let $\delta=1/(n^3T)$ and $L=\lceil\log_2T\rceil$.
--
--   **Exposure.** Level $\ell$ is *exposed* to the fake user of round $t$ if the sampled level is $\ell_t=\ell$ and the user is fake (p. 52); the exposure of $\ell$ is the number of such rounds.
--
--   **Windows and the events $\mathcal G^{(\ell)}_{i,t}$.** For every $i$, $t$, $\ell$,
--   $$w^{(\ell)}_{i,t}=\sqrt{\frac32\,\frac{\log(4nT/\delta)}{\max(\hat\eta^{(\ell)}_{i,t},1)}}+\frac{\log(2L/\delta)+4}{\max(\hat\eta^{(\ell)}_{i,t},1)}\quad(21),\qquad \mathcal G^{(\ell)}_{i,t}=\big\{\hat r^{(\ell)}_{i,t}-w^{(\ell)}_{i,t}\le\mu_i\le\hat r^{(\ell)}_{i,t}+w^{(\ell)}_{i,t}\big\}\quad(22).$$
--
--   **Definition 1 (Event $\mathcal G$).** With $\ell^\star=\lceil\log_2F\rceil$, let $\mathcal G_1=\bigcap_{t\in[T],\,\ell\ge\ell^\star,\,i\in[n]}\mathcal G^{(\ell)}_{i,t}$, let $\mathcal G_2$ be the event that every level $\ell\ge\ell^\star$ is exposed to at most $\log(2L/\delta)+3$ fake users over the horizon, and $\mathcal G=\mathcal G_1\cap\mathcal G_2$.
--
--   **Thresholds.**
--   $$\gamma_{j,i}=\frac{64\log(4nT/\delta)}{\Delta_{j,i}^2}\quad(23).$$
--
--   These are the objects of Lemmas 6, 9 and 15.
--
--   **Formalization Note.** Levels are 0-based: Lean level $k$ is paper level $k+1$, and $\ell\ge\ell^\star$ is written $F\le2^{k+1}$ (every level when $F=0$). The events are predicates on trajectories; the state "at the end of round $t$" is FORC's state after processing the first $t$ rounds, and $\mathcal G_1$ ranges over $t=1,\dots,T$. The algorithm's own window (Step 10) divides by $\hat\eta$ itself; only the event uses $\max(\hat\eta,1)$, as in the paper.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 28, (21)–(22); p. 29, Definition 1, (23); p. 52, App. D.1

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm

namespace FakeUserRanking.FORC

open scoped BigOperators

variable {n T : ℕ}

/-- FORC's state at the end of round `t` of trajectory `τ` (after Steps 8–11 of the first `t`
rounds); `t = 0` is the initial state. -/
noncomputable def stateAt
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : ℕ) : State n (numLevels T) :=
  forcState n T tb fb (algHist τ t)

/-- The number of fake users level `k` (paper level `k + 1`) is exposed to over the horizon
(p. 52): rounds whose sampled level is `k` and whose user is fake. -/
def exposure {L : ℕ} (k : Fin L) (τ : Fin T → Step n L) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => (τ s).1 = k ∧ (τ s).2.1.isSome)).card

/-- The window (21), p. 28, extended to `η̂ = 0`:
`w^(ℓ)_{i,t} = √((3/2) log(4nT/δ) / max(η̂^(ℓ)_{i,t}, 1)) + (log(2L/δ) + 4) / max(η̂^(ℓ)_{i,t}, 1)`. -/
noncomputable def window21 (n T : ℕ) {L : ℕ} (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  Real.sqrt ((3 / 2) * Real.log (4 * n * T / delta n T) / max (etaHat st k i) 1) +
    (Real.log (2 * L / delta n T) + 4) / max (etaHat st k i) 1

/-- Event `G₂` (Definition 1, p. 29): every level `ℓ ≥ ℓ⋆ = ⌈log₂ F⌉` (Lean: `F ≤ 2^(k+1)`) is
exposed to at most `log(2L/δ) + 3` fake users. -/
noncomputable def goodG2 (F : ℕ) (τ : Fin T → Step n (numLevels T)) : Prop :=
  ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) →
    (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 3

/-- Event `G₁` (Definition 1, p. 29, with (21)–(22)): at the end of every round `t ∈ [T]`, for
every level `ℓ ≥ ℓ⋆` and every product `i`, `r̂^(ℓ)_{i,t} − w^(ℓ)_{i,t} ≤ μ_i ≤ r̂^(ℓ)_{i,t} + w^(ℓ)_{i,t}`. -/
noncomputable def goodG1 (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) → ∀ i : Fin n,
    rHat (stateAt tb fb τ t) k i - window21 n T (stateAt tb fb τ t) k i ≤ inst.μ i ∧
      inst.μ i ≤ rHat (stateAt tb fb τ t) k i + window21 n T (stateAt tb fb τ t) k i

/-- The good event `G = G₁ ∩ G₂` (Definition 1, p. 29). -/
noncomputable def goodEvent (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  goodG1 inst F tb fb τ ∧ goodG2 F τ

/-- `γ_{j,i} = 64 log(4nT/δ) / Δ²_{j,i}` (23), p. 29. -/
noncomputable def gamma (T : ℕ) (inst : Instance n) (j i : Fin n) : ℝ :=
  64 * Real.log (4 * n * T / delta n T) / gap inst j i ^ 2

end FakeUserRanking.FORC


