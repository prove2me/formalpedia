-- Prove2me | Definitions.Def_LearnCollude_Policy
-- name    : LearnCollude_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:04:12.691988+00:00
-- url     : https://prove2.me/theorems/6de54d8c-653a-4e95-a497-ba4a23f5f4e4
-- title:
--   The Composite SPSA policy (10), the sub-algorithms (11), (12), and the relative regret (8)
-- statement:
--   Fix $\theta_{a,i}>0$, $\theta_{c,i}\in(0,p_i^{\max}/2)$, and $a_{n,i}=\theta_{a,i}/n$, $c_{n,i}=\theta_{c,i}/n^{1/4}$. Let $P_I(x)=\min\{\max\{i_{\min},x\},i_{\max}\}$ for $I=[i_{\min},i_{\max}]$, and $I_i(n)=[c_{n,i},p_i^{\max}-c_{n,i}]$. Initial estimates lie in $(0,p_i^{\max})$. The observed revenue at period $t$ is $\tilde r_i(t)=p_i(t)(d_i(p(t))+\epsilon_i(t))$.
--
--   **The Composite SPSA policy**, used by both firms, keeps estimates $\hat p^{col},\hat p^{com}$ with counters $n^{col},n^{com}$ starting at $1$. In an exploration phase of arm $a$, an odd $\tau$ charges $\hat p_i^a+c_{n^a,i}\,\omega_i^a(n^a)$ and an even $\tau$ charges $\hat p_i^a-c_{n^a,i}\,\omega_i^a(n^a)$, after which
--   $$
--   \hat p_i^{a}\leftarrow P_{I_i(n^a)}\Big(\hat p_i^{a}+a_{n^a,i}\,\frac{\pi_i^{+}-\pi_i^{-}}{2\,\omega_i^{a}(n^a)\,c_{n^a,i}}\Big),\qquad n^a\leftarrow n^a+1,
--   $$
--   where $\pi_i^\pm=\sum_j\tilde r_j^\pm$ for $a=col$ and $\pi_i^\pm=\tilde r_i^\pm$ for $a=com$. In an estimation phase of arm $a$ both firms charge $\hat p^a$, and the sums $\hat r_k^a$ of the revenues over that phase are recorded. In the exploitation phase the collusive arm runs if $\hat r_k^{col}>\hat r_k^{com}$ for both $k$, and the competitive arm otherwise.
--
--   **The sub-algorithms** (11), (12) run one such recursion alone, with periods paired: pair $n$ is periods $2n-1$ and $2n$.
--
--   **The relative regret** of firm $i$ for a price process $p$ is
--   $$
--   \Delta_i(T)=\frac{\sum_{t=1}^T\mathbb E[r_i(p^*)-r_i(p(t))]}{T\cdot r_i(p^*)}.
--   $$
--
--   **Formalization Note** $p(t)$ and the observations are defined by one deterministic recursion on the state, for given coins and noise, and then evaluated on the sample space. Counters and periods start at $1$, so the junk value at $0$ of $a_{n,i}$ and $c_{n,i}$ is never used. Typos of (10) are fixed: $\hat p_k^{col}$, $\omega_k$ in the exploitation update are $\hat p_i^{col}$, $\omega_i$, and $n^{com}=n^{col}+1$ is $n^{com}=n^{com}+1$. An odd phase 5 ends with the first period of a pair and no update.
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), policy (10), p. 14; (11), (12), p. 15; eq. (8), p. 10

import Mathlib
import Definitions.Def_LearnCollude_Assumption1
import Definitions.Def_LearnCollude_Randomness
import Definitions.Def_LearnCollude_Schedule

open MeasureTheory

namespace LearnCollude

/-- **The tuning constants** `θ_a,i > 0` and `θ_c,i ∈ (0, pmaxᵢ / 2)`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), policy (10), p. 14. -/
structure Gains (M : Model) where
  /-- The constants `θ_a,i`. -/
  θa : Fin 2 → ℝ
  /-- The constants `θ_c,i`. -/
  θc : Fin 2 → ℝ
  θa_pos : ∀ i, 0 < θa i
  θc_pos : ∀ i, 0 < θc i
  θc_lt : ∀ i, θc i < M.pmax i / 2

/-- The initial estimates lie in the open price intervals: `p̂^a_i(1) ∈ (0, pmaxᵢ)`. -/
def IsInitial (M : Model) (h₀ : Arm → Fin 2 → ℝ) : Prop :=
  ∀ a i, h₀ a i ∈ Set.Ioo 0 (M.pmax i)

variable {M : Model}

/-- The step size `a_{n,i} = θ_a,i / n`. Counters start at `n = 1`, so the value `0` at `n = 0` is
never used. -/
noncomputable def Gains.a (G : Gains M) (n : ℕ) (i : Fin 2) : ℝ := G.θa i / n

/-- The perturbation size `c_{n,i} = θ_c,i / n^{1/4}`. Counters start at `n = 1`, so the value `0` at
`n = 0` is never used. -/
noncomputable def Gains.c (G : Gains M) (n : ℕ) (i : Fin 2) : ℝ := G.θc i / (n : ℝ) ^ (1 / 4 : ℝ)

/-- The projection `P_I(x) = min{max{lo, x}, hi}` onto `I = [lo, hi]`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), p. 13. -/
noncomputable def projI (lo hi x : ℝ) : ℝ := min (max lo x) hi

/-- The perturbed price `(hᵢ + sgn · c_{n,i} · wᵢ)ᵢ`, with `sgn = 1` for the first and `sgn = −1` for
the second period of a pair. -/
noncomputable def perturbed (G : Gains M) (n : ℕ) (w h : Fin 2 → ℝ) (sgn : ℝ) : Prices :=
  WithLp.toLp 2 fun i => h i + sgn * G.c n i * w i

/-- The revenues `pᵢ d̃ᵢ = pᵢ (dᵢ(p) + eᵢ)` observed at the price `p` with noise `e`. -/
noncomputable def observe (M : Model) (p : Prices) (e : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => p i * (M.d i p + e i)

/-- The part of the observed revenues that drives firm `i`'s update: the sum over both firms on the
collusive arm, and its own revenue on the competitive arm. -/
def payoff : Arm → Fin 2 → (Fin 2 → ℝ) → ℝ
  | Arm.col, _, R => ∑ j, R j
  | Arm.com, i, R => R i

/-- **The SPSA update** of policy (10), Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), p. 14:
`hᵢ ↦ P_{Iᵢ(n)}(hᵢ + a_{n,i} (π⁺ − π⁻) / (2 wᵢ c_{n,i}))`, for `Iᵢ(n) = [c_{n,i}, pmaxᵢ − c_{n,i}]`,
where `π^±` is `Σ_j R_j^±` on the collusive arm and `R_i^±` on the competitive arm. -/
noncomputable def spsaUpdate (G : Gains M) (a : Arm) (n : ℕ) (w h Rp Rm : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  fun i => projI (G.c n i) (M.pmax i - G.c n i)
    (h i + G.a n i * ((payoff a i Rp - payoff a i Rm) / (2 * w i * G.c n i)))

/-- The state of policy (10) between two periods, common to both firms: the estimates `p̂^a(n^a)`, the
counters `n^a`, the revenues of the pending first period of a pair, and the running sums of the
revenues of the estimation phases of the current cycle. -/
structure State where
  /-- The current estimates. -/
  hat : Arm → Fin 2 → ℝ
  /-- The counters `ncol`, `ncom`. -/
  cnt : Arm → ℕ
  /-- The revenues `r̃⁺` of the last first period of a pair. -/
  rPlus : Fin 2 → ℝ
  /-- The sums `r̂^a_k` over the estimation phases of the current cycle. -/
  est : Arm → Fin 2 → ℝ

open Classical in
/-- The decision of phase 5: the collusive arm if `r̂^col_k > r̂^com_k` for both `k`, and the
competitive arm otherwise. -/
noncomputable def decision (st : State) : Arm :=
  if ∀ k, st.est Arm.com k < st.est Arm.col k then Arm.col else Arm.com

/-- The arm in use at period `t`. -/
noncomputable def activeArm (S : Schedule) (st : State) (t : ℕ) : Arm :=
  match S.phaseOf t with
  | Phase.explore a => a
  | Phase.estimate a => a
  | Phase.exploit => decision st

open Classical in
/-- The prices charged at period `t`, by policy (10), Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), p. 14: the estimate itself in an estimation phase; otherwise the estimate of the
active arm plus (`τ` odd) or minus (`τ` even) the perturbation.

**Formalization Note** The competitive arm's parity is printed as that of `τ − 4⌊N_c^α⌋`, which equals
the parity of `τ`. -/
noncomputable def chargedPrice (G : Gains M) (S : Schedule) (coin : Arm → Fin 2 → ℕ → ℝ) (st : State)
    (t : ℕ) : Prices :=
  let a := activeArm S st t
  let n := st.cnt a
  match S.phaseOf t with
  | Phase.estimate _ => WithLp.toLp 2 (st.hat a)
  | _ => perturbed G n (fun i => coin a i n) (st.hat a) (if Odd (S.tau t) then 1 else -1)

open Classical in
/-- **One period of policy (10)**, for both firms at once, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), p. 14. The sums `r̂` restart at `τ = 1`. In an estimation phase the revenues are
added to `r̂^a`. Otherwise an odd `τ` records the revenues `r̃⁺`, and an even `τ` makes the SPSA update
of the active arm with the recorded `r̃⁺` and the current `r̃⁻`, and raises its counter.

**Formalization Note** Typos of (10) are fixed: the `p̂_k^col`, `ω_k` of the exploitation update are
`p̂_i^col`, `ω_i`, and `n^com = n^col + 1` is `n^com = n^com + 1`. If phase 5 has odd length, its last
period charges the first price of a pair and makes no update; the next pair of that arm uses the
same counter. -/
noncomputable def nextState (M : Model) (G : Gains M) (S : Schedule) (coin : Arm → Fin 2 → ℕ → ℝ)
    (eps : Fin 2 → ℕ → ℝ) (t : ℕ) (st₀ : State) : State :=
  let st : State := if S.tau t = 1 then { st₀ with est := fun _ _ => 0 } else st₀
  let a := activeArm S st t
  let n := st.cnt a
  let R := observe M (chargedPrice G S coin st t) (fun i => eps i t)
  match S.phaseOf t with
  | Phase.estimate b =>
      { st with est := Function.update st.est b (fun k => st.est b k + R k) }
  | _ =>
      if Odd (S.tau t) then { st with rPlus := R }
      else
        { st with
          hat := Function.update st.hat a
            (spsaUpdate G a n (fun i => coin a i n) (st.hat a) st.rPlus R)
          cnt := Function.update st.cnt a (n + 1) }

/-- The state of policy (10) at the start: estimates `h₀`, counters `1`. -/
def initState (h₀ : Arm → Fin 2 → ℝ) : State where
  hat := h₀
  cnt := fun _ => 1
  rPlus := fun _ => 0
  est := fun _ _ => 0

/-- The state after period `t`, for coins `coin` and noise `eps`. -/
noncomputable def run (M : Model) (G : Gains M) (S : Schedule) (h₀ : Arm → Fin 2 → ℝ)
    (coin : Arm → Fin 2 → ℕ → ℝ) (eps : Fin 2 → ℕ → ℝ) : ℕ → State
  | 0 => initState h₀
  | t + 1 => nextState M G S coin eps (t + 1) (run M G S h₀ coin eps t)

/-- The price vector `p(t)`, `t ≥ 1`, when both firms use the **Composite SPSA policy** (10) with the
tuning `G`, `S`, `h₀`, `α = 3/5`, on the randomness `ρ`. -/
noncomputable def compositePrice {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ2 : ℝ}
    (M : Model) (G : Gains M) (S : Schedule) (h₀ : Arm → Fin 2 → ℝ) (ρ : Randomness μ σ2)
    (t : ℕ) (x : Ω) : Prices :=
  chargedPrice G S (fun a i n => ρ.ω a i n x)
    (run M G S h₀ (fun a i n => ρ.ω a i n x) (fun i t => ρ.ε i t x) (t - 1)) t

/-- The time average `(1/T) Σ_{t=1}^T p(t)`. -/
noncomputable def averagePrice {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ2 : ℝ}
    (M : Model) (G : Gains M) (S : Schedule) (h₀ : Arm → Fin 2 → ℝ) (ρ : Randomness μ σ2)
    (T : ℕ) (x : Ω) : Prices :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, compositePrice M G S h₀ ρ t x

/-- The sum `r̂^a_k` of the estimation phase of arm `a` in cycle `c`, as it stands at the start of
phase 5 of that cycle. -/
noncomputable def cycleEstimate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ2 : ℝ}
    (M : Model) (G : Gains M) (S : Schedule) (h₀ : Arm → Fin 2 → ℝ) (ρ : Randomness μ σ2)
    (c : ℕ) (a : Arm) (k : Fin 2) (x : Ω) : ℝ :=
  (run M G S h₀ (fun a i n => ρ.ω a i n x) (fun i t => ρ.ε i t x)
    (S.s c + 8 * S.f c)).est a k

/-- The iterates of the sub-algorithm (11) (`a = col`) or (12) (`a = com`) after `m` updates, both
firms running it, with periods paired: pair `n = m + 1` is periods `2n − 1` and `2n`. -/
noncomputable def subIterate (M : Model) (G : Gains M) (a : Arm) (h₀ : Fin 2 → ℝ)
    (coin : Fin 2 → ℕ → ℝ) (eps : Fin 2 → ℕ → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => h₀
  | m + 1 =>
    let n := m + 1
    let w : Fin 2 → ℝ := fun i => coin i n
    let h := subIterate M G a h₀ coin eps m
    spsaUpdate G a n w h
      (observe M (perturbed G n w h 1) fun i => eps i (2 * n - 1))
      (observe M (perturbed G n w h (-1)) fun i => eps i (2 * n))

/-- The estimate `p̂^a(n)`, `n ≥ 1`, of the sub-algorithm (11) or (12), Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), p. 15, on the randomness `ρ`.

**Formalization Note** The noise of period `t` is `ρ.ε i t`, and the coins of the unused arm are
ignored. As `ρ` is arbitrary, the statements on this recursion also cover its embedding in policy
(10), where the pairs of a recursion run at random times. -/
noncomputable def subEstimate {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ2 : ℝ}
    (M : Model) (G : Gains M) (a : Arm) (h₀ : Fin 2 → ℝ) (ρ : Randomness μ σ2) (n : ℕ) (x : Ω) :
    Prices :=
  WithLp.toLp 2 (subIterate M G a h₀ (fun i n => ρ.ω a i n x) (fun i t => ρ.ε i t x) (n - 1))

/-- The price vector at period `t ≥ 1` under the sub-algorithm (11) or (12): pair `n = ⌈t / 2⌉`, with
the plus sign if `t` is odd and the minus sign if `t` is even. -/
noncomputable def subPrice {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ2 : ℝ}
    (M : Model) (G : Gains M) (a : Arm) (h₀ : Fin 2 → ℝ) (ρ : Randomness μ σ2) (t : ℕ) (x : Ω) :
    Prices :=
  open Classical in
  let n := (t + 1) / 2
  perturbed G n (fun i => ρ.ω a i n x) (subEstimate M G a h₀ ρ n x) (if Odd t then 1 else -1)

/-- The **relative regret** `Δᵢ(T) = Σ_{t=1}^T E[rᵢ(p*) − rᵢ(p(t))] / (T · rᵢ(p*))` of firm `i` for a
price process `p`, Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06), eq. (8), p. 10.

**Formalization Note** `rᵢ(p*) > 0` under Assumption 1 (there is a verification file). The revenue
loss is integrable for the processes of this mission: they are measurable, they stay in the box
(where `rᵢ` is continuous, hence bounded) except at the first pair of each arm, and there they take
finitely many values. -/
noncomputable def relativeRegret {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Assumption1 M) (i : Fin 2) (p : ℕ → Ω → Prices) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, ∫ x, (M.r i (pStar A) - M.r i (p t x)) ∂μ) / (T * M.r i (pStar A))

end LearnCollude


