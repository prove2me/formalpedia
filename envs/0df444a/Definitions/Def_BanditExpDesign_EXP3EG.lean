-- Prove2me | Definitions.Def_BanditExpDesign_EXP3EG
-- name    : BanditExpDesign_EXP3EG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:36.771682+00:00
-- url     : https://prove2.me/theorems/e392c0f6-df58-4db7-a89e-7da0b60a4bf4
-- title:
--   Algorithm 2 — EXP3EG: active sets, IPW estimates $\hat R_t$, propensities $\pi_t$, the policy, $\hat\Delta^{(i,j)}_t$ and the variance proxy
-- statement:
--   EXP3EG is the experimental design of Simchi-Levi and Wang: exponential weights over an active set of arms, elimination of arms that fall behind, and forced exploration of the eliminated arms. Given a stochastic bandit with reward laws $P_1,\dots,P_K$ on $\mathbb R$, inputs $\alpha\in[0,1]$ and $\delta$, set
--   $$C=(4K^2(e^2+1)+2)^2(\log(2/\delta))^2,\qquad \varepsilon_t=\frac1{\sqrt{Ct}},\qquad \alpha_t=\frac1{Kt^\alpha}.$$
--
--   Initialize $\mathcal A_1=\{1,\dots,K\}$ and $\hat R_0\equiv0$. For $t=1,2,\dots$:
--
--   1. For $a\in\mathcal A_t$ put $\pi_t(a)=(1-|\mathcal A_t^c|\alpha_t)\,e^{\varepsilon_{t-1}\hat R_{t-1}(a)}\big/\sum_{a'\in\mathcal A_t}e^{\varepsilon_{t-1}\hat R_{t-1}(a')}$, and for $a\notin\mathcal A_t$ put $\pi_t(a)=\alpha_t$.
--   2. Draw $A_t\sim\pi_t$ and observe $R_t$.
--   3. For every arm, $\hat R_t(a)=\hat R_{t-1}(a)+\frac{R_t}{\pi_t(a)}\mathbb I_{a=A_t}$.
--   4. $\mathcal A_{t+1}=\mathcal A_t\setminus\{a:\hat R_t^{\max}-\hat R_t(a)>2\sqrt{Ct}\}$, where $\hat R_t^{\max}=\max_{a\in\mathcal A_t}\hat R_t(a)$.
--
--   The output is the inverse-propensity-weighted estimate $\hat\Delta_t^{(i,j)}=\frac1t(\hat R_t(i)-\hat R_t(j))$ of the treatment effect $\Delta^{(i,j)}=\mu_i-\mu_j$.
--
--   The module also defines the martingale $M_t^{(i,j)}=t(\hat\Delta_t^{(i,j)}-\Delta^{(i,j)})$, the variance proxy $V_t^{(i,j)}=\sum_{s=1}^t(1/\pi_s(i)+1/\pi_s(j))$, the constant $C'=K^2(1+e^2)$, the condition $r_t(a)\in[-1,1]$, the history filtration $\mathcal H_s$ and the error $e(n,\hat\Delta)=\mathbb E|\Delta-\hat\Delta_n|$. These are the objects in which every statement of the mission is written.
--
--   **Formalization Note** EXP3EG is a deterministic function of the observed history, recursing on the state $(\mathcal A_{s+1},\hat R_s)$; $\hat R_t$ is never defined from the means. The policy is the published `BanditPolicy` whose kernel at a history of $n$ rounds is $\sum_a\pi_{n+1}(a)\delta_a$; that $\mathcal A_t\ne\emptyset$, that $\pi_t>0$ and $\sum_a\pi_t(a)=1$, and that the kernel is measurable are proved in the module. The maximum $\hat R_t^{\max}$ is over the active set: p.13 writes all arms, under which the active set can become empty, and the paper's proofs use the active-set maximum. $\varepsilon_0=0$ (the value is irrelevant since $\hat R_0=0$). The run is frozen after the history ends.
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, Algorithm 2, p.18; model §1.1, pp.3–4; error e(t, Δ̂) p.4; R̂^max p.13; M^(i,j)_t p.18; C′ = K²(1+e²) (EC.7), p.ec9; V_t(a) p.ec10 and §D.1, p.ec13

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

noncomputable section

namespace BanditExpDesign

/-! # EXP3EG: exponential weights, elimination and forced exploration

Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*, SSRN 4224969, Algorithm 2, p.18,
with the bandit model of §1.1, pp.3–4.

**Formalization Note.** The bandit is the published `BanditAlgorithm.StochasticBandit K` and a
policy is the published `BanditAlgorithm.BanditPolicy K`; the law of the first `n` rounds is the
published `BanditAlgorithm.banditMeasure ν π n`. Arms are `Fin K`. A history
`h : BanditHistory K n` holds rounds `1, …, n` of the paper in its coordinates `0, …, n - 1`:
coordinate `s : Fin n` is round `s + 1`, so `(h s).1` is `A_{s+1}` and `(h s).2` is `R_{s+1}`.
Everything below is a deterministic function of the observed history; `R̂_t` is computed by the
recursion of line 8, never from the means. The logarithm is natural and `e = Real.exp 1`.
`t ^ α` is `Real.rpow`. -/

/-- The constant `C = (4K²(e²+1)+2)²(log(2/δ))²` of Algorithm 2, line 2, p.18. -/
def constC (K : ℕ) (δ : ℝ) : ℝ :=
  (4 * (K : ℝ) ^ 2 * (Real.exp 1 ^ 2 + 1) + 2) ^ 2 * Real.log (2 / δ) ^ 2

/-- The constant `C' = K²(1+e²)` of (EC.7), p.ec9. -/
def constC' (K : ℕ) : ℝ := (K : ℝ) ^ 2 * (1 + Real.exp 1 ^ 2)

/-- The learning rate `ε_t = 1/√(Ct)` of Algorithm 2, line 4, p.18.

**Formalization Note.** The algorithm uses `ε_0` at `t = 1` and never defines it. Lean's `1/0 = 0`
gives `ε_0 = 0`, the value Algorithm 1 sets (p.14); it does not matter since `R̂_0 = 0`. -/
def learningRate (K : ℕ) (δ : ℝ) (t : ℕ) : ℝ := 1 / Real.sqrt (constC K δ * t)

/-- The forced-exploration probability `α_t = 1/(K t^α)` of Algorithm 2, line 4, p.18.
Only rounds `t ≥ 1` are used. -/
def exploreProb (K : ℕ) (α : ℝ) (t : ℕ) : ℝ := 1 / ((K : ℝ) * (t : ℝ) ^ α)

/-- The state of EXP3EG after `s` rounds: the active set `𝒜_{s+1}` for the next round and the
estimates `R̂_s`. -/
abbrev RunState (K : ℕ) := Finset (Fin K) × (Fin K → ℝ)

/-- The initial state: `𝒜_1 = {1, …, K}` and `R̂_0 = 0` (Algorithm 2, line 2, p.18). -/
def initState (K : ℕ) : RunState K := (Finset.univ, fun _ => 0)

/-- The propensities of round `s + 1` computed from the state after `s` rounds (Algorithm 2,
line 5, p.18): with `t = s + 1`,
`π_t(a) = (1 - |𝒜_tᶜ| α_t) e^{ε_{t-1} R̂_{t-1}(a)} / ∑_{a' ∈ 𝒜_t} e^{ε_{t-1} R̂_{t-1}(a')}` for
`a ∈ 𝒜_t`, and `π_t(a) = α_t` for `a ∉ 𝒜_t`. -/
def statePropensity (K : ℕ) (α δ : ℝ) (s : ℕ) (st : RunState K) (a : Fin K) : ℝ :=
  if a ∈ st.1 then
    (1 - (st.1ᶜ.card : ℝ) * exploreProb K α (s + 1)) * Real.exp (learningRate K δ s * st.2 a) /
      ∑ a' ∈ st.1, Real.exp (learningRate K δ s * st.2 a')
  else exploreProb K α (s + 1)

/-- `R̂^max` over the active set `A`: `max_{a ∈ A} R̂(a)` (`0` on the empty set, which never occurs
along a run: see `runState_active_nonempty`).

**Formalization Note.** p.13 writes the maximum over all arms; the maximum over the active set is
the rule the proofs of the paper use ((EC.9)–(EC.10), p.ec10) and the only one under which `𝒜_t`
stays nonempty. -/
def activeMax {K : ℕ} (A : Finset (Fin K)) (R : Fin K → ℝ) : ℝ :=
  if hA : A.Nonempty then A.sup' hA R else 0

/-- One round of EXP3EG (Algorithm 2, lines 8–9, p.18): from the state after `s` rounds and the
observed pair `(A_{s+1}, R_{s+1})`, with `t = s + 1`, set
`R̂_t(a) = R̂_{t-1}(a) + (R_t / π_t(a)) 𝟙{a = A_t}` and
`𝒜_{t+1} = 𝒜_t \ {a : R̂_t^max - R̂_t(a) > 2√(Ct)}`. -/
def stateStep (K : ℕ) (α δ : ℝ) (s : ℕ) (st : RunState K) (obs : Fin K × ℝ) : RunState K :=
  let R' : Fin K → ℝ := fun a =>
    st.2 a + if a = obs.1 then obs.2 / statePropensity K α δ s st a else 0
  (st.1.filter (fun a => ¬ (activeMax st.1 R' - R' a > 2 * Real.sqrt (constC K δ * ((s + 1 : ℕ) : ℝ)))),
    R')

/-- The state of EXP3EG after `s` rounds of the history `h`. The run is frozen once `h` is
exhausted (`s ≥ n`); statements use it for `s ≤ n` only. -/
def runState {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) : ℕ → RunState K
  | 0 => initState K
  | s + 1 =>
      if hs : s < n then stateStep K α δ s (runState α δ h s) (h ⟨s, hs⟩)
      else runState α δ h s

/-- The IPW estimate `R̂_s(a)` of the cumulative reward of arm `a` after `s` rounds of `h`
(Algorithm 2, line 8, p.18). -/
def ipwEstimate {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (s : ℕ) (a : Fin K) : ℝ :=
  (runState α δ h s).2 a

/-- The active set `𝒜_t` of round `t ≥ 1` along `h`: `activeSet α δ h 1 = univ`, and `𝒜_t` depends
on the first `t - 1` rounds. Statements use `t ≥ 1` only. -/
def activeSet {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (t : ℕ) : Finset (Fin K) :=
  (runState α δ h (t - 1)).1

/-- The propensity `π_t(a)` of round `t ≥ 1` along `h`; it depends on the first `t - 1` rounds.
Statements use `t ≥ 1` only. -/
def propensity {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (t : ℕ) (a : Fin K) : ℝ :=
  statePropensity K α δ (t - 1) (runState α δ h (t - 1)) a

/-- The IPW estimate `Δ̂_t^{(i,j)} = (R̂_t(i) - R̂_t(j)) / t` of Algorithm 2, line 10, p.18. -/
def ateEstimate {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (t : ℕ) (i j : Fin K) : ℝ :=
  (1 / (t : ℝ)) * (ipwEstimate α δ h t i - ipwEstimate α δ h t j)

/-- The treatment effect `Δ^{(i,j)} = μ_i - μ_j` (p.3). -/
def ate {K : ℕ} (ν : StochasticBandit K) (i j : Fin K) : ℝ :=
  banditArmMean ν i - banditArmMean ν j

/-- The paper's standing reward condition `r_t(a) ∈ [-1,1]` (p.3): every reward law is carried by
`[-1, 1]`. -/
def RewardsBounded {K : ℕ} (ν : StochasticBandit K) : Prop :=
  ∀ a, ν.P a (Set.Icc (-1) 1) = 1

/-- The variance proxy `V_t^{(i,j)} = ∑_{s=1}^t (1/π_s(i) + 1/π_s(j))` (p.ec12; the sum as named on
p.ec13, §D.1). -/
def varianceProxy {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (t : ℕ) (i j : Fin K) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, (1 / propensity α δ h s i + 1 / propensity α δ h s j)

/-- The martingale `M_t^{(i,j)} = t (Δ̂_t^{(i,j)} - Δ^{(i,j)})` (p.18). -/
def ateMartingale {K n : ℕ} (ν : StochasticBandit K) (α δ : ℝ) (h : BanditHistory K n) (t : ℕ)
    (i j : Fin K) : ℝ :=
  (t : ℝ) * (ateEstimate α δ h t i j - ate ν i j)

/-- The IPW difference `(R_t/π_t(i)) 𝟙{A_t=i} - (R_t/π_t(j)) 𝟙{A_t=j}` of round `t = s + 1`. -/
def ipwDifference {K n : ℕ} (α δ : ℝ) (h : BanditHistory K n) (s : Fin n) (i j : Fin K) : ℝ :=
  ((h s).2 / propensity α δ h ((s : ℕ) + 1) i) * (if (h s).1 = i then 1 else 0) -
    ((h s).2 / propensity α δ h ((s : ℕ) + 1) j) * (if (h s).1 = j then 1 else 0)

/-- The history filtration on `BanditHistory K n`: `historyFiltration K n s` is generated by rounds
`1, …, s`, i.e. it is `ℋ_s` of the paper (constant for `s ≥ n`). -/
def historyFiltration (K n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (BanditHistory K n))
    where
  seq s := ⨆ (r : Fin n) (_ : (r : ℕ) < s), MeasurableSpace.comap (fun h => h r) inferInstance
  mono' := fun _ _ hst => iSup₂_le fun r hr =>
    le_iSup₂_of_le r (lt_of_lt_of_le hr hst) le_rfl
  le' := fun _ => iSup₂_le fun r _ => (measurable_pi_apply r).comap_le

/-- The estimation error `e(n, Δ̂^{(i,j)}) = E[|Δ^{(i,j)} - Δ̂_n^{(i,j)}|]` (p.4) of a policy `π`
paired with an estimate `est` of `Δ^{(i,j)}` computed from the history of `n` rounds. -/
def estimationError {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (n : ℕ)
    (est : BanditHistory K n → ℝ) (i j : Fin K) : ℝ :=
  ∫ h, |est h - ate ν i j| ∂(banditMeasure ν π n)

/-! ## The run is well defined

The active set stays nonempty, the propensities are a positive probability vector, and they are
measurable in the history. These are the facts needed to make EXP3EG a `BanditPolicy`. -/

section WellDefined

variable {K : ℕ} {α δ : ℝ}

lemma stateStep_active_nonempty (s : ℕ) (st : RunState K) (obs : Fin K × ℝ)
    (hst : st.1.Nonempty) : (stateStep K α δ s st obs).1.Nonempty := by
  obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup' hst
    (fun a => st.2 a + if a = obs.1 then obs.2 / statePropensity K α δ s st a else 0)
  refine ⟨b, ?_⟩
  simp only [stateStep, Finset.mem_filter]
  refine ⟨hb, ?_⟩
  simp only [activeMax, dif_pos hst, hmax]
  simp only [sub_self, gt_iff_lt, not_lt]
  positivity

/-- The active set never empties. -/
lemma runState_active_nonempty {n : ℕ} [NeZero K] (h : BanditHistory K n) (s : ℕ) :
    (runState α δ h s).1.Nonempty := by
  induction s with
  | zero =>
      exact (Finset.univ_nonempty_iff.mpr ⟨(0 : Fin K)⟩ : (Finset.univ : Finset (Fin K)).Nonempty)
  | succ s ih =>
      rw [runState]
      split_ifs
      · exact stateStep_active_nonempty s _ _ ih
      · exact ih

lemma exploreProb_pos [NeZero K] (s : ℕ) : 0 < exploreProb K α (s + 1) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hs : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
  exact one_div_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos hs α))

lemma exploreProb_le [NeZero K] (hα : 0 ≤ α) (s : ℕ) :
    exploreProb K α (s + 1) ≤ 1 / (K : ℝ) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hs : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have h1 : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ α := Real.one_le_rpow hs hα
  unfold exploreProb
  apply one_div_le_one_div_of_le hK
  nlinarith

/-- `1 - |𝒜ᶜ| α_t ≥ 1/K` for a nonempty active set. -/
lemma active_mass_lower [NeZero K] (hα : 0 ≤ α) (s : ℕ) (A : Finset (Fin K)) (hA : A.Nonempty) :
    1 / (K : ℝ) ≤ 1 - (Aᶜ.card : ℝ) * exploreProb K α (s + 1) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hcard : (Aᶜ.card : ℝ) ≤ (K : ℝ) - 1 := by
    have h1 : 1 ≤ A.card := hA.card_pos
    have h2 : Aᶜ.card + A.card = K := by
      simp [Finset.card_compl_add_card A]
    have h3 : (Aᶜ.card : ℝ) + (A.card : ℝ) = K := by exact_mod_cast h2
    have h4 : (1 : ℝ) ≤ A.card := by exact_mod_cast h1
    linarith
  have hp := exploreProb_le (K := K) hα s
  have hp0 := (exploreProb_pos (K := K) (α := α) s).le
  have hc0 : (0 : ℝ) ≤ Aᶜ.card := by positivity
  have : (Aᶜ.card : ℝ) * exploreProb K α (s + 1) ≤ ((K : ℝ) - 1) * (1 / (K : ℝ)) :=
    mul_le_mul hcard hp hp0 (by linarith)
  have h5 : ((K : ℝ) - 1) * (1 / (K : ℝ)) = 1 - 1 / (K : ℝ) := by
    field_simp
  linarith

lemma statePropensity_pos [NeZero K] (hα : 0 ≤ α) (s : ℕ) (st : RunState K) (hst : st.1.Nonempty)
    (a : Fin K) : 0 < statePropensity K α δ s st a := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  unfold statePropensity
  split_ifs with ha
  · have h1 := active_mass_lower (K := K) hα s st.1 hst
    have h2 : (0 : ℝ) < 1 / (K : ℝ) := by positivity
    apply div_pos (mul_pos (by linarith) (Real.exp_pos _))
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hst
  · exact exploreProb_pos s

lemma statePropensity_sum (s : ℕ) (st : RunState K) (hst : st.1.Nonempty) :
    ∑ a, statePropensity K α δ s st a = 1 := by
  classical
  set p := exploreProb K α (s + 1)
  set w : Fin K → ℝ := fun a => Real.exp (learningRate K δ s * st.2 a)
  have hW : ∑ a ∈ st.1, w a ≠ 0 :=
    (Finset.sum_pos (fun _ _ => Real.exp_pos _) hst).ne'
  rw [← Finset.sum_add_sum_compl st.1]
  have h1 : ∑ a ∈ st.1, statePropensity K α δ s st a = 1 - (st.1ᶜ.card : ℝ) * p := by
    have : ∀ a ∈ st.1, statePropensity K α δ s st a =
        (1 - (st.1ᶜ.card : ℝ) * p) * w a / ∑ a' ∈ st.1, w a' := by
      intro a ha
      simp only [statePropensity, if_pos ha, p, w]
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self hW,
      mul_one]
  have h2 : ∑ a ∈ st.1ᶜ, statePropensity K α δ s st a = (st.1ᶜ.card : ℝ) * p := by
    have : ∀ a ∈ st.1ᶜ, statePropensity K α δ s st a = p := by
      intro a ha
      simp only [statePropensity, if_neg (Finset.mem_compl.mp ha), p]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  ring

/-- `π_{s+1}(a) > 0` along every history. -/
lemma propensity_pos {n : ℕ} [NeZero K] (hα : 0 ≤ α) (h : BanditHistory K n) (s : ℕ) (a : Fin K) :
    0 < statePropensity K α δ s (runState α δ h s) a :=
  statePropensity_pos hα s _ (runState_active_nonempty h s) a

/-- `∑_a π_{s+1}(a) = 1` along every history. -/
lemma propensity_sum {n : ℕ} [NeZero K] (h : BanditHistory K n) (s : ℕ) :
    ∑ a, statePropensity K α δ s (runState α δ h s) a = 1 :=
  statePropensity_sum s _ (runState_active_nonempty h s)

local instance : MeasurableSpace (Finset (Fin K)) := ⊤

local instance : DiscreteMeasurableSpace (Finset (Fin K)) := ⟨fun _ => trivial⟩

lemma measurable_finset_of_mem {X : Type*} [MeasurableSpace X] (f : X → Finset (Fin K))
    (hf : ∀ a, MeasurableSet {x | a ∈ f x}) : Measurable f := by
  classical
  refine measurable_to_countable' fun S => ?_
  have : f ⁻¹' {S} = ⋂ a, (if a ∈ S then {x | a ∈ f x} else {x | a ∈ f x}ᶜ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.ext_iff]
    refine forall_congr' fun a => ?_
    by_cases ha : a ∈ S <;> simp [ha]
  rw [this]
  refine MeasurableSet.iInter fun a => ?_
  split_ifs
  · exact hf a
  · exact (hf a).compl

/-- For a fixed active set, the propensity is measurable in the estimates. -/
lemma measurable_statePropensity (s : ℕ) (A : Finset (Fin K)) (a : Fin K) :
    Measurable (fun R : Fin K → ℝ => statePropensity K α δ s (A, R) a) := by
  unfold statePropensity
  by_cases ha : a ∈ A
  · simp only [ha, if_true]
    refine Measurable.div ?_ ?_
    · exact ((measurable_pi_apply a).const_mul _).exp.const_mul _
    · exact Finset.measurable_sum _ fun b _ => ((measurable_pi_apply b).const_mul _).exp
  · simp only [ha, if_false]
    exact measurable_const

lemma measurable_activeMax (A : Finset (Fin K)) {X : Type*} [MeasurableSpace X]
    (R : X → Fin K → ℝ) (hR : ∀ a, Measurable fun x => R x a) :
    Measurable (fun x => activeMax A (R x)) := by
  unfold activeMax
  by_cases hA : A.Nonempty
  · simp only [dif_pos hA]
    have := Finset.measurable_sup' hA (f := fun a x => R x a) (fun a _ => hR a)
    convert this using 2 with x
    simp [Finset.sup'_apply]
  · simp only [dif_neg hA]
    exact measurable_const

lemma measurable_stateStep (s : ℕ) :
    Measurable (fun p : RunState K × (Fin K × ℝ) => stateStep K α δ s p.1 p.2) := by
  -- reduce to fixed active set and fixed arm
  have hfix : ∀ (A : Finset (Fin K)) (b : Fin K),
      Measurable (fun q : (Fin K → ℝ) × ℝ => stateStep K α δ s (A, q.1) (b, q.2)) := by
    intro A b
    have hR : ∀ a, Measurable (fun q : (Fin K → ℝ) × ℝ =>
        q.1 a + if a = b then q.2 / statePropensity K α δ s (A, q.1) a else 0) := by
      intro a
      refine ((measurable_pi_apply a).comp measurable_fst).add ?_
      by_cases hab : a = b
      · simp only [hab, if_true]
        exact measurable_snd.div ((measurable_statePropensity s A b).comp measurable_fst)
      · simp only [hab, if_false]
        exact measurable_const
    refine Measurable.prodMk ?_ (measurable_pi_iff.mpr hR)
    refine measurable_finset_of_mem _ fun a => ?_
    by_cases ha : a ∈ A
    · have : {x : (Fin K → ℝ) × ℝ | a ∈ (stateStep K α δ s (A, x.1) (b, x.2)).1} =
          {x | ¬ (activeMax A (fun c => x.1 c + if c = b then x.2 / statePropensity K α δ s (A, x.1) c
              else 0) - (x.1 a + if a = b then x.2 / statePropensity K α δ s (A, x.1) a else 0) >
            2 * Real.sqrt (constC K δ * ((s + 1 : ℕ) : ℝ)))} := by
        ext x
        simp [stateStep, ha]
      change MeasurableSet {x : (Fin K → ℝ) × ℝ | a ∈ (stateStep K α δ s (A, x.1) (b, x.2)).1}
      rw [this]
      refine MeasurableSet.compl ?_
      exact measurableSet_lt measurable_const
        ((measurable_activeMax A _ hR).sub (hR a))
    · have : {x : (Fin K → ℝ) × ℝ | a ∈ (stateStep K α δ s (A, x.1) (b, x.2)).1} = ∅ := by
        ext x
        simp [stateStep, ha]
      change MeasurableSet {x : (Fin K → ℝ) × ℝ | a ∈ (stateStep K α δ s (A, x.1) (b, x.2)).1}
      rw [this]
      exact MeasurableSet.empty
  -- glue over the finitely many active sets and arms
  have hglue : Measurable (fun p : (Finset (Fin K) × Fin K) × ((Fin K → ℝ) × ℝ) =>
      stateStep K α δ s (p.1.1, p.2.1) (p.1.2, p.2.2)) :=
    measurable_from_prod_countable_right fun c => hfix c.1 c.2
  have heq : (fun p : RunState K × (Fin K × ℝ) => stateStep K α δ s p.1 p.2) =
      (fun p : (Finset (Fin K) × Fin K) × ((Fin K → ℝ) × ℝ) =>
        stateStep K α δ s (p.1.1, p.2.1) (p.1.2, p.2.2)) ∘
      (fun p : RunState K × (Fin K × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := rfl
  rw [heq]
  refine hglue.comp ?_
  exact (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
    (measurable_fst.snd.prodMk measurable_snd.snd)

attribute [local irreducible] stateStep in
lemma measurable_stateStep_comp {X : Type*} [MeasurableSpace X] (s : ℕ) {f : X → RunState K}
    {g : X → Fin K × ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => stateStep K α δ s (f x) (g x)) :=
  by
  have h1 := hf.prodMk hg
  have h2 := measurable_stateStep (K := K) (α := α) (δ := δ) s
  exact Measurable.comp (f := fun x => (f x, g x)) h2 h1

lemma measurable_runState {n : ℕ} (s : ℕ) :
    Measurable (fun h : BanditHistory K n => runState α δ h s) := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
      by_cases hs : s < n
      · have : (fun h : BanditHistory K n => runState α δ h (s + 1)) =
            fun h => stateStep K α δ s (runState α δ h s) (h ⟨s, hs⟩) := by
          funext h
          rw [runState, dif_pos hs]
        rw [this]
        exact measurable_stateStep_comp s (f := fun h : BanditHistory K n => runState α δ h s)
          (g := fun h : BanditHistory K n => h ⟨s, hs⟩) ih (measurable_pi_apply (⟨s, hs⟩ : Fin n))
      · have : (fun h : BanditHistory K n => runState α δ h (s + 1)) =
            fun h => runState α δ h s := by
          funext h
          rw [runState, dif_neg hs]
        rw [this]
        exact ih

/-- `π_{n+1}` is a measurable function of the history of the first `n` rounds. -/
lemma measurable_propensity_next {n : ℕ} (a : Fin K) :
    Measurable (fun h : BanditHistory K n => statePropensity K α δ n (runState α δ h n) a) := by
  have hglue : Measurable (fun p : Finset (Fin K) × (Fin K → ℝ) =>
      statePropensity K α δ n p a) :=
    measurable_from_prod_countable_right (fun A => measurable_statePropensity n A a)
  exact hglue.comp (measurable_runState n)

end WellDefined

/-- The law `∑_a π_{n+1}(a) δ_a` of `A_{n+1}` given the history of the first `n` rounds
(Algorithm 2, lines 5–6, p.18). -/
def selectionLaw (K : ℕ) (α δ : ℝ) {n : ℕ} (h : BanditHistory K n) : Measure (Fin K) :=
  ∑ a, ENNReal.ofReal (statePropensity K α δ n (runState α δ h n) a) • Measure.dirac a

/-- EXP3EG (Algorithm 2, p.18) with inputs `α ∈ [0,1]` and `δ`, as a `BanditPolicy`: given the
history of the first `n` rounds, the next arm is drawn from `π_{n+1}`.

**Formalization Note.** `K ≠ 0` and `α ∈ [0,1]` are needed for `π_t` to be a probability vector, so
they are arguments of the definition. `δ` is free: `C` is a real number for every `δ`, and the
theorems of the mission assume `δ ∈ (0, 2/e)`. -/
def exp3eg (K : ℕ) [NeZero K] (α δ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) : BanditPolicy K where
  select n :=
    { toFun := fun h => selectionLaw K α δ h
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
        simp only [selectionLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
          smul_eq_mul]
        exact Finset.measurable_sum _ fun a _ =>
          ((measurable_propensity_next a).ennreal_ofReal).mul_const _ }
  markov n := ⟨fun h => ⟨by
    have hpos := fun a => (propensity_pos (δ := δ) hα.1 h n a).le
    show selectionLaw K α δ h Set.univ = 1
    simp only [selectionLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hpos a), propensity_sum h n, ENNReal.ofReal_one]⟩⟩

end BanditExpDesign

end


