-- Prove2me | Definitions.Def_ExploreFirst_FundIneq_FullHistory
-- name    : ExploreFirst_FundIneq_FullHistory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:57.003901+00:00
-- url     : https://prove2.me/theorems/a3b4963d-d863-4f36-b757-ba8783370608
-- title:
--   §1.1–§2, pp. 3–7 — auxiliary-uniform information, measurable strategies, history law and pull counts
-- statement:
--   The information $I_t$ consists of the independent auxiliary uniforms $U_0,\ldots,U_t$ and rewards $Y_1,\ldots,Y_t$. A strategy chooses the next arm as a measurable function of $I_t$. Initially $U_0$ is uniform on $[0,1]$; after a strategy chooses arm $a$, the next reward has law $\nu_a$ and the next auxiliary uniform is independent and uniform. Iterating this kernel gives the law of $I_T$. The number of pulls of arm $a$ is the sum of indicators that the strategy selected $a$ at each prefix $I_t$, and its expectation is taken under the law of $I_T$.
--
--   **Formalization Note.** This explicit information process retains the uniforms used by the paper's strategy. `FullHistory`, `FullStrategy`, `fullHistoryMeasure`, `fullPullCount`, and `fullExpPulls` implement the objects in §1.1 and equation (7). Arms use `Fin K` and are indexed from zero.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 3–7, §1.1 and (7)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory ProbabilityTheory

namespace ExploreFirst.FundIneq

/-- The information `I_t = (U₀, Y₁, U₁, …, Y_t, U_t)` of §1.1, p. 3. -/
abbrev FullHistory (t : ℕ) := (Fin (t + 1) → unitInterval) × (Fin t → ℝ)

/-- A strategy as on p. 3: the next arm is a measurable function of `I_t`. -/
structure FullStrategy (K : ℕ) where
  select : (t : ℕ) → FullHistory t → Fin K
  measurable_select : ∀ t, Measurable (select t)

/-- Append the next reward and the next independent uniform to `I_t`. -/
def fullHistorySnoc {t : ℕ} (p : FullHistory t × (ℝ × unitInterval)) :
    FullHistory (t + 1) :=
  (Fin.snoc p.1.1 p.2.2, Fin.snoc p.1.2 p.2.1)

/-- Under a strategy, the next reward has the selected arm's law and the new auxiliary
uniform is independent. This is (7) on p. 7. -/
noncomputable def fullStepKernel {K : ℕ} (ν : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) (t : ℕ) : Kernel (FullHistory t) (ℝ × unitInterval) :=
  ((BanditAlgorithm.banditRewardKernel ν).comap (ψ.select t) (ψ.measurable_select t)).compProd
    (Kernel.const (FullHistory t × ℝ) (volume : Measure unitInterval))

/-- The law of `I_T`, starting with `U₀` uniform and iterating (7). -/
noncomputable def fullHistoryMeasure {K : ℕ} (ν : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) : (T : ℕ) → Measure (FullHistory T)
  | 0 => (volume : Measure unitInterval).map
      (fun u => ((fun _ : Fin 1 => u), (fun i : Fin 0 => i.elim0)))
  | t + 1 => ((fullHistoryMeasure ν ψ t).compProd (fullStepKernel ν ψ t)).map
      fullHistorySnoc

/-- The prefix `I_t` of `I_T`, for a round indexed by `t < T`. -/
def fullHistoryPrefix {T : ℕ} (h : FullHistory T) (t : Fin T) : FullHistory t.val :=
  ((fun i => h.1 (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt t.isLt)) i)),
   (fun i => h.2 (Fin.castLE (Nat.le_of_lt t.isLt) i)))

/-- Number of pulls of an arm by time `T`, read from the full information `I_T`. -/
def fullPullCount {K T : ℕ} (ψ : FullStrategy K) (a : Fin K)
    (h : FullHistory T) : ℕ :=
  ∑ t : Fin T, if ψ.select t.val (fullHistoryPrefix h t) = a then 1 else 0

/-- Expected number of pulls, the weight in (6). -/
noncomputable def fullExpPulls {K : ℕ} (ν : BanditAlgorithm.StochasticBandit K)
    (ψ : FullStrategy K) (T : ℕ) (a : Fin K) : ℝ :=
  ∫ h, (fullPullCount ψ a h : ℝ) ∂(fullHistoryMeasure ν ψ T)

end ExploreFirst.FundIneq


