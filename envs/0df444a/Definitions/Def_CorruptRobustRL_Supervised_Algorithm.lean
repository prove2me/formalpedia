-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Algorithm
-- name    : CorruptRobustRL_Supervised_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:12.029839+00:00
-- url     : https://prove2.me/theorems/6654dd4e-51a1-40f0-887b-ba6aeb6aac08
-- title:
--   §3–4.3, pp. 10–17 — UCBVI-BASE, the nested active sets of SuperVIsed.C, the layer schedule (3.3), master policies, $q_\ell$, $\ell_\star$ and the terms $\Delta$ of Theorem 4.1
-- statement:
--   This file defines one episode of SuperVIsed.C (Algorithms 1 and 2) and the quantities of Theorem 4.1.
--
--   **UCBVI-BASE (Algorithm 2).** A base learner receives active sets $\mathcal A_h(x)$, a global model-estimate $(\hat r_{\mathrm{gl}},\hat p_{\mathrm{gl}},b_{\mathrm{gl}})$ and a subsampled one $(\hat r_{\mathrm{sb}},\hat p_{\mathrm{sb}},b_{\mathrm{sb}})$. With $\bar V_{H+1}=\underline V_{H+1}=0$ it computes, for $h=H,\dots,1$,
--   $$\bar Q_h=\min\{H,\ \hat r_{\mathrm{gl}}+\hat p_{\mathrm{gl}}^\top\bar V_{h+1}+b_{\mathrm{gl}},\ \hat r_{\mathrm{sb}}+\hat p_{\mathrm{sb}}^\top\bar V_{h+1}+b_{\mathrm{sb}}\},\qquad \underline Q_h=\max\{0,\ \hat r_{\mathrm{gl}}+\hat p_{\mathrm{gl}}^\top\underline V_{h+1}-b_{\mathrm{gl}},\ \hat r_{\mathrm{sb}}+\hat p_{\mathrm{sb}}^\top\underline V_{h+1}-b_{\mathrm{sb}}\},$$
--   the base policy $\pi^{\mathrm{base}}_h(x)\in\arg\max_{a\in\mathcal A_h(x)}\bar Q_h(x,a)$, $\bar V_h(x)=\bar Q_h(x,\pi^{\mathrm{base}}_h(x))$, $\underline V_h(x)=\max_{a\in\mathcal A_h(x)}\underline Q_h(x,a)$, and the active sets handed down, $\{a\in\mathcal A_h(x):\bar Q_h(x,a)\ge\underline V_h(x)\}$. Its Q-supervisor is $(\bar Q,\underline Q,\mathcal A,\pi^{\mathrm{base}})$.
--
--   **Nested learners (Algorithm 1).** Learners $\ell=\ell_{\max},\dots,1$ run in turn: learner $\ell_{\max}$ has $\mathcal A\equiv\mathcal A$ (all actions), and learner $\ell-1$ receives the active sets handed down by learner $\ell$. Learner $\ell$ uses the global estimates $(\hat r_{\mathrm{gl}},\hat p_{\mathrm{gl}})$ with its own global bonus $b_{\mathrm{gl},\ell}$, and its own subsampled model $(\hat r_{\mathrm{sb},\ell},\hat p_{\mathrm{sb},\ell},b_{\mathrm{sb},\ell})$; its Q-supervisor is $\mathcal T_\ell$.
--
--   **Layer schedule (3.3).** From layer $f$, the next layer is $n\in\{f+1,\dots,\ell_{\max}\}$ with probability $\frac1{2nH}2^{-(n-f)}$ and stays $f$ with the remaining probability. Starting from $\ell_0=1$, the schedule $(\ell_1,\dots,\ell_H)\sim\mathcal D^{\mathrm{sched}}$ draws each $\ell_h$ from this law given $\ell_{h-1}$; under schedule $(\ell_h)$ the master policy plays $\pi^{\mathrm{base}}_{\ell_h}$ at stage $h$. With $q_\ell=P[\ell_H=\ell]$ and $q_{\le\ell}=P[\ell_H\le\ell]$, the master policy $\pi^{\mathrm{master}}$ is the mixture over schedules with weights $\mathcal D^{\mathrm{sched}}$, and $\pi^{\mathrm{master}}_\ell$, $\pi^{\mathrm{master}}_{\le\ell}$ are the mixtures conditioned on $\ell_H=\ell$ and on $\ell_H\le\ell$ (Definition 4.6).
--
--   **Theorem 4.1's quantities.** $\ell_\star=\min\{\ell\ge1:2^\ell\ge C\}$. For a Q-supervisor $\mathcal T$ with $\mathcal V_{h+1}=\{\bar V_{h+1}-V^\star_{h+1},\ \bar V_{h+1}-\underline V_{h+1}\}$,
--   $$\Delta_{\ell}=E^{\pi^{\mathrm{master}}_{\ell}}\Big[\sum_{h=1}^H\max\Big(0,\min\Big(3H,\ 2b_{\mathrm{sb},\ell}(x_h,a_h)+\max_{V\in\mathcal V_{\ell;h+1}}(\hat p_{\mathrm{sb},\ell}(x_h,a_h)-p^\star(x_h,a_h))^\top V\Big)\Big)\Big],$$
--   and $\Delta_{\le\ell}$ is the same with $\pi^{\mathrm{master}}_{\le\ell}$, $b_{\mathrm{gl},\ell}$ and $\hat p_{\mathrm{gl}}$.
--
--   **Formalization Note** Stages are 0-based in Lean: the paper's stage $h\in[H]$ is Lean's `h - 1`, and the terminal values $V_{H+1}\equiv0$ sit at Lean index `H`. Schedules are functions `Fin H → Fin ℓmax`, decoded to layers $1,\dots,\ell_{\max}$ by adding one. The argmax of line 9 is an argument `sel : Selector A` and theorems quantify over every `sel` satisfying `IsArgmaxSelector`, so no tie-break is privileged. If the set of line 11 is empty, the learner hands down its own active sets; footnote 16 asserts that this set is never empty, which holds whenever the learner's Q-supervisor is confidence-admissible, so the convention changes nothing there. $\ell_\star$ is `max 1 (Nat.clog 2 C)`. The summand of $\Delta$ carries a positive part $\max(0,\cdot)$ that Theorem 4.1 does not print; see that theorem's note. The conditioned weights divide by $q_\ell$, which is positive for every layer $\ell\in[\ell_{\max}]$ when $H\ge1$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, pp. 10–12, (3.3), Algorithm 1 (lines 3, 7–13), Algorithm 2; pp. 15–17, Definitions 4.6, 4.8, Theorem 4.1 ($\ell_\star$, $\mathcal V$, $\Delta$)

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

variable {X A : Type}

/-! ### UCBVI-BASE (Algorithm 2, p. 12) for one base learner -/

/-- An argmax selector: `sel s f` is meant to be an element of `s` maximizing `f` over `s`. -/
abbrev Selector (A : Type) := Finset A → (A → ℝ) → A

/-- The specification of an argmax selector on nonempty sets (Algorithm 2, line 9, "arg max"). -/
def IsArgmaxSelector (sel : Selector A) : Prop :=
  ∀ (s : Finset A) (f : A → ℝ), s.Nonempty → sel s f ∈ s ∧ ∀ a ∈ s, f a ≤ f (sel s f)

/-- The maximum of `f` over a finite set `s`; `0` on the empty set (never used on one, see
`nextAct`). -/
noncomputable def maxOn (s : Finset A) (f : A → ℝ) : ℝ :=
  if hne : s.Nonempty then s.sup' hne f else 0

/-- One-step backup `r̂(x, a) + p̂(x, a)ᵀ V` of a model-estimate. -/
noncomputable def backup [Fintype X] (m : ModelEst X A) (V : X → ℝ) (x : X) (a : A) : ℝ :=
  m.r x a + ∑ x', m.p x a x' * V x'

/-- Line 7: `Q̄ = min{H, r̂_gl + p̂_glᵀ V̄ + b_gl, r̂_sb + p̂_sbᵀ V̄ + b_sb}`. -/
noncomputable def qUp [Fintype X] (H : ℕ) (gl sb : ModelEst X A) (Vb : X → ℝ) (x : X) (a : A) : ℝ :=
  min (H : ℝ) (min (backup gl Vb x a + gl.b x a) (backup sb Vb x a + sb.b x a))

/-- Line 8: `Q̲ = max{0, r̂_gl + p̂_glᵀ V̲ − b_gl, r̂_sb + p̂_sbᵀ V̲ − b_sb}`. -/
noncomputable def qLow [Fintype X] (gl sb : ModelEst X A) (Vl : X → ℝ) (x : X) (a : A) : ℝ :=
  max 0 (max (backup gl Vl x a - gl.b x a) (backup sb Vl x a - sb.b x a))

/-- The pair `(V̄, V̲)` of Algorithm 2 at the 0-based stage `H − n`, by backward recursion on the
number `n` of remaining stages (lines 3, 6–10): `(V̄_{H+1}, V̲_{H+1}) = (0, 0)`, then
`V̄_h(x) = Q̄_h(x, π^base_h(x))` and `V̲_h(x) = max_{a ∈ 𝒜_h(x)} Q̲_h(x, a)`. -/
noncomputable def ucbviVals [Fintype X] (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) : ℕ → (X → ℝ) × (X → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | n + 1 =>
    (fun x => qUp H gl sb (ucbviVals H act gl sb sel n).1 x
        (sel (act (H - (n + 1)) x) (qUp H gl sb (ucbviVals H act gl sb sel n).1 x)),
     fun x => maxOn (act (H - (n + 1)) x) (qLow gl sb (ucbviVals H act gl sb sel n).2 x))

/-- The Q-supervisor `(Q̄, Q̲, 𝒜, π^base)` produced by UCBVI-BASE run with active sets `act`, global
model-estimate `gl`, subsampled model-estimate `sb` and argmax selector `sel` (Algorithm 2,
lines 6–10; the supervisor `𝒯_{k,ℓ}` of p. 15). At stage `h < H`, `Q̄_h` and `Q̲_h` back up the
values of stage `h + 1`. -/
noncomputable def ucbviSup [Fintype X] (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) : QSupervisor X A where
  Qbar h x a := qUp H gl sb (ucbviVals H act gl sb sel (H - (h + 1))).1 x a
  Qlow h x a := qLow gl sb (ucbviVals H act gl sb sel (H - (h + 1))).2 x a
  act := act
  ucb h x := sel (act h x) (fun a => qUp H gl sb (ucbviVals H act gl sb sel (H - (h + 1))).1 x a)

/-- Line 11: the active sets handed to the next base learner,
`𝒜_{ℓ−1;h}(x) = {a ∈ 𝒜_h(x) : Q̄_h(x, a) ≥ V̲_h(x)}`. Convention: if this set is empty, the
learner's own set `𝒜_h(x)` is handed down instead (footnote 16 asserts the set is never empty;
that holds whenever the learner's supervisor is confidence-admissible). -/
noncomputable def nextAct [Fintype X] (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A)
    (sel : Selector A) (h : ℕ) (x : X) : Finset A := by
  classical
  exact
    let T := ucbviSup H act gl sb sel
    let s := (act h x).filter (fun a => maxOn (act h x) (T.Qlow h x) ≤ T.Qbar h x a)
    if s.Nonempty then s else act h x

/-! ### One episode of SuperVIsed.C (Algorithm 1, p. 11) -/

/-- The model-estimates available in one episode `k` (Definition 4.8): global estimates
`(r̂_gl, p̂_gl)` shared by all learners, the global bonus `b_{gl,ℓ}` of learner `ℓ`, and the
subsampled model `(r̂_{sb,ℓ}, p̂_{sb,ℓ}, b_{sb,ℓ})` of learner `ℓ`. -/
structure EpisodeEst (X A : Type) where
  rgl : X → A → ℝ
  pgl : X → A → X → ℝ
  bgl : ℕ → X → A → ℝ
  rsb : ℕ → X → A → ℝ
  psb : ℕ → X → A → X → ℝ
  bsb : ℕ → X → A → ℝ

/-- The global model-estimate `𝔪_{ℓ;gl} = (r̂_gl, p̂_gl, b_{gl,ℓ})` of learner `ℓ`. -/
def EpisodeEst.gl (E : EpisodeEst X A) (ℓ : ℕ) : ModelEst X A := ⟨E.rgl, E.pgl, E.bgl ℓ⟩

/-- The subsampled model-estimate `𝔪_{ℓ;sb} = (r̂_{sb,ℓ}, p̂_{sb,ℓ}, b_{sb,ℓ})` of learner `ℓ`. -/
def EpisodeEst.sb (E : EpisodeEst X A) (ℓ : ℕ) : ModelEst X A := ⟨E.rsb ℓ, E.psb ℓ, E.bsb ℓ⟩

/-- Active sets of the learner `ℓmax − d` (Algorithm 1, lines 3, 7–8): learner `ℓmax` has
`𝒜 ≡ A`, and learner `ℓ − 1` receives `nextAct` of learner `ℓ`. -/
noncomputable def layerActAux [Fintype X] [Fintype A] (H ℓmax : ℕ) (E : EpisodeEst X A)
    (sel : Selector A) : ℕ → ℕ → X → Finset A
  | 0 => fun _ _ => univ
  | d + 1 => nextAct H (layerActAux H ℓmax E sel d) (E.gl (ℓmax - d)) (E.sb (ℓmax - d)) sel

/-- The active sets `𝒜_{k,ℓ}` of learner `ℓ ∈ [ℓmax]`. -/
noncomputable def layerAct [Fintype X] [Fintype A] (H ℓmax : ℕ) (E : EpisodeEst X A)
    (sel : Selector A) (ℓ : ℕ) : ℕ → X → Finset A :=
  layerActAux H ℓmax E sel (ℓmax - ℓ)

/-- The Q-supervisor `𝒯_{k,ℓ} = (Q̄_{k,ℓ}, Q̲_{k,ℓ}, 𝒜_{k,ℓ}, π^base_{k,ℓ})` of learner `ℓ`
(p. 15); its UCB policy is the base policy `π^base_{k,ℓ}`. -/
noncomputable def layerSup [Fintype X] [Fintype A] (H ℓmax : ℕ) (E : EpisodeEst X A)
    (sel : Selector A) (ℓ : ℕ) : QSupervisor X A :=
  ucbviSup H (layerAct H ℓmax E sel ℓ) (E.gl ℓ) (E.sb ℓ) sel

/-- The base policies `ℓ ↦ π^base_{k,ℓ}` of one episode. -/
noncomputable def basePolicies [Fintype X] [Fintype A] (H ℓmax : ℕ) (E : EpisodeEst X A)
    (sel : Selector A) (ℓ : ℕ) : DetPolicy X A :=
  (layerSup H ℓmax E sel ℓ).ucb

/-! ### The layer schedule (3.3) and the master policies (Definition 4.6) -/

/-- `P[D_f = n]`, the probability that the current layer `f` is resampled to `n` (3.3):
`(1/(2nH))·2^{−(n−f)}` for `n ∈ {f+1, …, ℓmax}`, the remaining probability for `n = f`, and `0`
otherwise. -/
noncomputable def stepProb (H ℓmax f n : ℕ) : ℝ :=
  if f < n ∧ n ≤ ℓmax then 1 / (2 * n * H) * (2 : ℝ)⁻¹ ^ (n - f)
  else if n = f then 1 - ∑ m ∈ Ioc f ℓmax, 1 / (2 * m * H) * (2 : ℝ)⁻¹ ^ (m - f)
  else 0

/-- A layer schedule `(ℓ₁, …, ℓ_H) ∈ [ℓmax]^H`, encoded with values in `Fin ℓmax`. -/
abbrev Sched (H ℓmax : ℕ) := Fin H → Fin ℓmax

/-- The layer `ℓ_{t+1} ∈ {1, …, ℓmax}` of a schedule at the 0-based stage `t`. -/
def Sched.lay {H ℓmax : ℕ} (s : Sched H ℓmax) (t : Fin H) : ℕ := (s t : ℕ) + 1

/-- The final layer `ℓ_H` (`1`, the initial layer, if `H = 0`). -/
def Sched.last {H ℓmax : ℕ} (s : Sched H ℓmax) : ℕ :=
  if hH : 0 < H then s.lay ⟨H - 1, Nat.sub_lt hH Nat.one_pos⟩ else 1

/-- The probability of a schedule under `𝒟^sched` (Algorithm 1, lines 9–11): starting from the layer
`ℓ₀ = 1`, each `ℓ_t` is drawn from `D_{ℓ_{t−1}}`. -/
noncomputable def schedWeight {H ℓmax : ℕ} (s : Sched H ℓmax) : ℝ :=
  ∏ t : Fin H,
    stepProb H ℓmax
      (if (t : ℕ) = 0 then 1
        else s.lay ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩)
      (s.lay t)

/-- `P[ℓ_{t+1} = f]` under `𝒟^sched`, for the 0-based stage `t`. -/
noncomputable def layerProb (H ℓmax : ℕ) (t : Fin H) (f : ℕ) : ℝ :=
  ∑ s : Sched H ℓmax, if s.lay t = f then schedWeight s else 0

/-- `P[ℓ_{t+1} = f ∧ ℓ_H = f]` under `𝒟^sched`. -/
noncomputable def layerStayProb (H ℓmax : ℕ) (t : Fin H) (f : ℕ) : ℝ :=
  ∑ s : Sched H ℓmax, if s.lay t = f ∧ s.last = f then schedWeight s else 0

/-- `q_ℓ = P[ℓ_H = ℓ]` (Definition 4.6). -/
noncomputable def q (H ℓmax ℓ : ℕ) : ℝ :=
  ∑ s : Sched H ℓmax, if s.last = ℓ then schedWeight s else 0

/-- `q_{≤ℓ} = P[ℓ_H ≤ ℓ]` (Definition 4.6). -/
noncomputable def qLe (H ℓmax ℓ : ℕ) : ℝ :=
  ∑ s : Sched H ℓmax, if s.last ≤ ℓ then schedWeight s else 0

/-- The deterministic Markov policy followed under schedule `s`: at stage `t` play
`π^base_{ℓ_t;t}` (Algorithm 1, lines 12–13). Stages `t ≥ H` never occur. -/
def schedPolicy {H ℓmax : ℕ} (base : ℕ → DetPolicy X A) (s : Sched H ℓmax) : DetPolicy X A :=
  fun t x => if ht : t < H then base (s.lay ⟨t, ht⟩) t x else base 1 t x

/-- The master policy `π^master_k`: the schedule is drawn from `𝒟^sched`. -/
noncomputable def master (H ℓmax : ℕ) (base : ℕ → DetPolicy X A) : Mixture X A where
  ι := Sched H ℓmax
  w := fun s => schedWeight s
  σ := schedPolicy base

/-- `π^master_{k,ℓ}` (Definition 4.6, item 1): the schedule is drawn from `𝒟^sched` conditioned on
`ℓ_H = ℓ`. -/
noncomputable def masterEq (H ℓmax : ℕ) (base : ℕ → DetPolicy X A) (ℓ : ℕ) : Mixture X A where
  ι := Sched H ℓmax
  w := fun s => if s.last = ℓ then schedWeight s / q H ℓmax ℓ else 0
  σ := schedPolicy base

/-- `π^master_{k,≤ℓ}` (Definition 4.6, item 2): the schedule is drawn from `𝒟^sched` conditioned on
`ℓ_H ≤ ℓ`. -/
noncomputable def masterLe (H ℓmax : ℕ) (base : ℕ → DetPolicy X A) (ℓ : ℕ) : Mixture X A where
  ι := Sched H ℓmax
  w := fun s => if s.last ≤ ℓ then schedWeight s / qLe H ℓmax ℓ else 0
  σ := schedPolicy base

/-- The critically tolerant layer `ℓ⋆ = min{ℓ ≥ 1 : 2^ℓ ≥ C}` (Theorem 4.1). -/
def lstar (C : ℕ) : ℕ := max 1 (Nat.clog 2 C)

/-! ### The per-episode suboptimality terms of Theorem 4.1 -/

/-- The summand of `Δ` (Theorem 4.1), with a positive part:
`max(0, min(3H, 2b(x, a) + max_{V ∈ 𝒱_{h+1}} (p̂(x, a) − p⋆(x, a))ᵀ V))`, where
`𝒱_{h+1} = {V̄_{h+1} − V⋆_{h+1}, V̄_{h+1} − V̲_{h+1}}` is formed from the Q-supervisor `T`. -/
noncomputable def deltaTerm [Fintype X] [Fintype A] [Nonempty A] (M : NominalMDP X A) (H : ℕ)
    (T : QSupervisor X A) (b : X → A → ℝ) (phat : X → A → X → ℝ) (h : ℕ) (x : X) (a : A) : ℝ :=
  max 0 (min (3 * (H : ℝ))
    (2 * b x a +
      max (∑ x', (phat x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vstar M H (h + 1) x'))
          (∑ x', (phat x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vlow H T (h + 1) x'))))

/-- `Δ_{k,ℓ} = E^{π^master_{k,ℓ}}[Σ_h max(0, min(3H, 2b_{sb,ℓ} + max_{V ∈ 𝒱_{ℓ;h+1}} (p̂_{sb,ℓ} − p⋆)ᵀ V))]`. -/
noncomputable def deltaEq [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (ℓ : ℕ) : ℝ :=
  mixExpect M H (masterEq H ℓmax (basePolicies H ℓmax E sel) ℓ)
    (deltaTerm M H (layerSup H ℓmax E sel ℓ) (E.bsb ℓ) (E.psb ℓ))

/-- `Δ_{k,≤ℓ} = E^{π^master_{k,≤ℓ}}[Σ_h max(0, min(3H, 2b_{gl,ℓ} + max_{V ∈ 𝒱_{ℓ;h+1}} (p̂_gl − p⋆)ᵀ V))]`. -/
noncomputable def deltaLe [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (ℓ : ℕ) : ℝ :=
  mixExpect M H (masterLe H ℓmax (basePolicies H ℓmax E sel) ℓ)
    (deltaTerm M H (layerSup H ℓmax E sel ℓ) (E.bgl ℓ) E.pgl)

end CorruptRobustRL.Supervised


