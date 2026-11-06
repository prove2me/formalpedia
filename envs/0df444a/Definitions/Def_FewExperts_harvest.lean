-- Prove2me | Definitions.Def_FewExperts_harvest
-- name    : FewExperts_harvest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:10.952782+00:00
-- url     : https://prove2.me/theorems/ab947ab7-dafd-4076-8d2e-1970ce1cc729
-- title:
--   HarvestGain$(\ell,\widetilde T,\mathcal B)$ (Algorithm 3), its transition, failure, and bad indices
-- statement:
--   **HarvestGain$(\ell,\widetilde T,\mathcal B)$** runs for $\widetilde T$ rounds against a baseline $\mathcal B$. Rounds are counted from the start of the run, and $G_t^i-G_t^{\mathcal B}$ is the lead of expert $i$ over $\mathcal B$ after round $t$.
--
--   1. If $\widetilde T=1$, it follows $\mathcal B$ for one round and does not stop.
--   2. Otherwise it draws for each expert an index $r_i\in\{1,\dots,K\}$, independently, with $\Pr[r_i\le j]=p^{K-j}$, and follows $\mathcal B$.
--   3. The **transition** happens at the first round $t^*<\widetilde T$ at which $G_t^i-G_t^{\mathcal B}\ge r_i\alpha\ell$ for some expert. It uses the first such expert $i^*$, with index $r^*=r_{i^*}$. If there is no transition, the run follows $\mathcal B$ to the end and never stops.
--   4. After a transition the run subscribes to $i^*$ and sets $\widetilde T'=\min(\lfloor\widetilde T/2\rfloor,\widetilde T-t^*)$. It lets $\mathcal B'$ be the two-expert Hedge on $\mathcal B$ and $i^*$, started at $t^*$ with horizon $\widetilde T'$. It then follows the recursive run $\mathcal A'=$ HarvestGain$(\ell,\widetilde T',\mathcal B')$, which draws fresh thresholds.
--   5. The run stops at the first round $t\in\{t^*+1,\dots,t^*+\widetilde T'\}$ at which $\mathcal A'$ stops, or $G_t^{i^*}-G_t^{\mathcal B}\ge(r^*+1)\alpha\ell$, or $t=t^*+\widetilde T'$.
--
--   A run **fails** if it stops at a round $t$ with $G_t^{\mathcal A}<G_t^{\mathcal B}+\alpha\ell-16\sqrt{\widetilde T}$. For an expert $i$ and $j\ge1$, let $t_j$ be the first round $t\le\widetilde T$ with $G_t^i-G_t^{\mathcal B}\ge j\alpha\ell$ ($t_j=\infty$ if there is none). An index $1\le j\le K$ is **bad** for $i$ if $t_j<\infty$ and $t_{j+1}>t_j+\widetilde T/2$.
--
--   HarvestGain is the subroutine of Proposition 2. It either gains $\Omega(\ell)$ over $\mathcal B$ or stops before any expert's lead over $\mathcal B$ grows by more than $O(\ell\log T)$.
--
--   **Formalization Note** The randomness is a threshold tape: one uniform variable per expert and recursion depth, independent under `thrTapeLaw`. A baseline is given by its mixed predictions on the run's rounds. The rate of $\mathcal B'$, which the paper leaves implicit, is $\sqrt{\ln 2/\widetilde T'}$, the rate of Lemma 2 for two experts. The record of a run holds its predictions, its stopping round and its subscriptions, which are the transition experts of all depths.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Algorithm 3 and its description, pp.16–17 (PDF pp.17–18); Proposition 2 (ii), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_FewExperts_alpha
import Definitions.Def_FewExperts_gainRegret
import Definitions.Def_FewExperts_hedgeWeights
import Definitions.Def_FewExperts_sampleFin

namespace FewExperts

open MeasureTheory

/-- A threshold tape: at recursion depth `d`, one uniform variable on `[0, 1]` per expert, from
which the expert's threshold index is drawn (`level`). Each recursion depth uses fresh,
independent thresholds (Algorithm 3, line 5, executed again by every recursive call). -/
abbrev ThrTape (N : ℕ) : Type := ℕ → Fin N → unitInterval

/-- The law of a threshold tape: all its uniform variables are independent and uniform on
`[0, 1]`. -/
noncomputable def thrTapeLaw (N : ℕ) : Measure (ThrTape N) :=
  Measure.infinitePi (fun _ : ℕ => Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))

/-- The law of one level of thresholds (one uniform variable per expert, independent). -/
noncomputable def levelLaw (N : ℕ) : Measure (Fin N → unitInterval) :=
  Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

/-- The threshold index `r_i ∈ {1, …, K}` drawn from the uniform variable `u`, with
`Pr[r_i ≤ j] = p^{K−j}` ((8), p.16; `K = ⌊1/α⌋`). -/
noncomputable def level (N T : ℕ) (u : unitInterval) : ℕ :=
  thrIndex (numLevels N T) (pT T) u

/-- The advantage `G_t^i − G_t^B` of expert `i` over the baseline with predictions `b`, after
round `t` of a run whose gains are `h` (round `1` is the first round of the run). -/
noncomputable def adv {N : ℕ} (h b : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  cumGain h t i - cumMix h b t

open Classical in
/-- The least expert satisfying `P` ("breaking ties by choosing the first expert", p.16). -/
noncomputable def firstFin {N : ℕ} (P : Fin N → Prop) (h : ∃ i, P i) : Fin N :=
  (Finset.univ.filter P).min'
    (by obtain ⟨i, hi⟩ := h; exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩)

open Classical in
/-- **The transition of HarvestGain** (Algorithm 3, lines 6–13, and p.16): the first round
`t* ∈ {1, …, T̃ − 1}` at which `G_t^i − G_t^B ≥ r_i α ℓ` for some expert `i`, the first such expert
`i*`, and its index `r* = r_{i*}`, where `r_i = level N T (u i)`. `none` if the run never
transitions. -/
noncomputable def transOf (N T : ℕ) (ℓ : ℝ) (Ttil : ℕ) (b h : ℕ → Fin N → ℝ)
    (u : Fin N → unitInterval) : Option (ℕ × Fin N × ℕ) :=
  if hex : ∃ t, 1 ≤ t ∧ t < Ttil ∧ ∃ i, (level N T (u i) : ℝ) * alpha N T * ℓ ≤ adv h b t i then
    let i := firstFin (fun i => (level N T (u i) : ℝ) * alpha N T * ℓ ≤ adv h b (Nat.find hex) i)
      (Nat.find_spec hex).2.2
    some (Nat.find hex, i, level N T (u i))
  else none

/-- The horizon `T̃′ = min(⌊T̃/2⌋, T̃ − t*)` of the second phase (Algorithm 3, line 14). -/
def phase2Horizon (Ttil ts : ℕ) : ℕ := min (Ttil / 2) (Ttil - ts)

/-- The two gain streams of the two-expert Hedge `B′` started at round `t*` (p.16): the (mixed)
gain of the baseline `B` and the gain of expert `i*`, at round `t* + u` (`u ≥ 1`). -/
noncomputable def pairStreams {N : ℕ} (b h : ℕ → Fin N → ℝ) (ts : ℕ) (is : Fin N) :
    Fin 2 → ℕ → ℝ :=
  ![fun u => mixGain h b (ts + u), fun u => h (ts + u) is]

/-- **The baseline `B′` of the second phase** (Algorithm 3, line 15; p.16: "Let B′ be the
two-expert Hedge algorithm from Lemma 2 run on B and i* for horizon T̃′, started at time t*").
Its prediction at its own round `u ≥ 1` (absolute run round `t* + u`) is the mixture
`w_u · B_{t*+u} + (1 − w_u) · δ_{i*}`, where `(w_u, 1 − w_u)` are Hedge's weights on the two
streams of `pairStreams`, with rate `√(ln 2 / T̃′)`.

**Formalization Note** The paper leaves `B′`'s learning rate implicit ("by Lemma 2"); it is
pinned to the rate `√(ln n / T)` of Lemma 2's Hedge with `n = 2` experts and horizon `T̃′`. -/
noncomputable def hedgePairPred {N : ℕ} (b h : ℕ → Fin N → ℝ) (ts : ℕ) (is : Fin N) (T' : ℕ) :
    ℕ → Fin N → ℝ :=
  fun u i =>
    hedgeAt (hedgeRate 2 T') (pairStreams b h ts is) u 0 * b (ts + u) i +
      hedgeAt (hedgeRate 2 T') (pairStreams b h ts is) u 1 * (if i = is then 1 else 0)

open Classical in
/-- The stopping round of the second phase (Algorithm 3, lines 19–24), counted from the start of
the second phase: the first `u ∈ {1, …, T̃′}` at which `A′` stops (`stopA = some u`), or the
threshold condition `cond u` holds, or `u = T̃′`. -/
noncomputable def phase2Stop (T' : ℕ) (stopA : Option ℕ) (cond : ℕ → Prop) : Option ℕ :=
  if hex : ∃ u, 1 ≤ u ∧ u ≤ T' ∧ (stopA = some u ∨ cond u ∨ u = T') then some (Nat.find hex)
  else none

/-- The record of a run of HarvestGain: its (mixed) prediction at each round `1, …, T̃` of the
run, its stopping round (`none` if it does not stop), and the set of experts it subscribes to
(the transition experts `i*` of all recursion depths). -/
structure HGRun (N : ℕ) where
  pred : ℕ → Fin N → ℝ
  stop : Option ℕ
  subs : Finset (Fin N)

/-- **HarvestGain(ℓ, T̃, B)** (Algorithm 3, p.16, and its description pp.16–17).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Algorithm 3, p.16 (PDF 17).

`harvest N T ℓ T̃ b h τ` is the run with parameter `ℓ`, horizon `T̃`, a baseline with (mixed)
predictions `b u` at the run's rounds `u = 1, …, T̃`, gains `h u i` at the run's rounds, and the
threshold tape `τ` (depth `0` for this run, depths `≥ 1` for the recursive runs).

* If `T̃ ≤ 1`, follow `B` and do not stop (line 3).
* Otherwise (lines 5–17), follow `B` until the transition `(t*, i*, r*) = transOf …`. If there is
  none, follow `B` until `T̃` and do not stop. If there is one, subscribe to `i*`, set
  `T̃′ = min(⌊T̃/2⌋, T̃ − t*)`, let `B′` be the two-expert Hedge on `B` and `i*` started at `t*`,
  and follow the recursive run `A′ = HarvestGain(ℓ, T̃′, B′)` on the next rounds, with fresh
  thresholds (the tape shifted by one depth) (lines 19–21).
* In the second phase, stop at the first round `t ∈ {t* + 1, …, t* + T̃′}` at which `A′` stops,
  or `G_t^{i*} − G_t^B ≥ (r* + 1) α ℓ` (gains from the start of the run, against the original
  `B`), or `t = t* + T̃′` (lines 22–24).

**Formalization Note** Rounds are 1-based and relative to the start of the run. The prediction
is defined at every round; after the second phase it is set to `B`'s (never read: the run has
stopped). Gains enter only through rounds before the current one, except in the stopping tests,
which are made after the round's gains are revealed (lines 8, 21). -/
noncomputable def harvest (N T : ℕ) (ℓ : ℝ) (Ttil : ℕ) (b h : ℕ → Fin N → ℝ) (τ : ThrTape N) :
    HGRun N :=
  if _hT : Ttil ≤ 1 then ⟨b, none, ∅⟩
  else
    match transOf N T ℓ Ttil b h (τ 0) with
    | none => ⟨b, none, ∅⟩
    | some (ts, is, rs) =>
      let A' := harvest N T ℓ (phase2Horizon Ttil ts) (hedgePairPred b h ts is (phase2Horizon Ttil ts))
        (fun u => h (ts + u)) (fun d => τ (d + 1))
      { pred := fun u => if u ≤ ts then b u
          else if u ≤ ts + phase2Horizon Ttil ts then A'.pred (u - ts) else b u
        stop := (phase2Stop (phase2Horizon Ttil ts) A'.stop
          (fun u => ((rs : ℝ) + 1) * alpha N T * ℓ ≤ adv h b (ts + u) is)).map (ts + ·)
        subs := insert is A'.subs }
termination_by Ttil
decreasing_by unfold phase2Horizon; omega

/-- The last round of a run that is covered by Proposition 2 (i): its stopping round, or `T̃` if
it does not stop ("up to and including the time at which the algorithm stops, or until it ends if
it does not stop", p.15). -/
def HGRun.stopOrEnd {N : ℕ} (A : HGRun N) (Ttil : ℕ) : ℕ := A.stop.getD Ttil

/-- **Failure** of a run (Proposition 2 (ii), (6), p.15): it stops, and at that round `t`,
`G_t^A < G_t^B + α ℓ − 16 √T̃`. -/
def HGRun.Fails {N : ℕ} (A : HGRun N) (α ℓ : ℝ) (Ttil : ℕ) (b h : ℕ → Fin N → ℝ) : Prop :=
  ∃ t, A.stop = some t ∧ cumMix h A.pred t < cumMix h b t + α * ℓ - 16 * Real.sqrt Ttil

open Classical in
/-- `t_j` of p.17 for the level `λ = jαℓ`: the first round `t ≤ T̃` with `G_t^i − G_t^B ≥ λ`
(`none` for `t_j = ∞`). -/
noncomputable def firstHit {N : ℕ} (h b : ℕ → Fin N → ℝ) (Ttil : ℕ) (i : Fin N) (lam : ℝ) :
    Option ℕ :=
  if hex : ∃ t, 1 ≤ t ∧ t ≤ Ttil ∧ lam ≤ adv h b t i then some (Nat.find hex) else none

/-- **Bad index** (p.17): "We say that an index 1 ≤ j ≤ 1/α is bad (for a given i) if t_j < ∞
and t_{j+1} > t_j + T̃/2, and good otherwise", with `t_j` the first round `t ≤ T̃` with
`G_t^i − G_t^B ≥ jαℓ` (`t_{j+1} = ∞` counts as `> t_j + T̃/2`). -/
def IsBadIndex (N T : ℕ) (ℓ : ℝ) (Ttil : ℕ) (b h : ℕ → Fin N → ℝ) (i : Fin N) (j : ℕ) : Prop :=
  1 ≤ j ∧ j ≤ numLevels N T ∧
    ∃ tj, firstHit h b Ttil i ((j : ℝ) * alpha N T * ℓ) = some tj ∧
      ∀ t', firstHit h b Ttil i (((j : ℝ) + 1) * alpha N T * ℓ) = some t' →
        (tj : ℝ) + (Ttil : ℝ) / 2 < t'

end FewExperts


