-- Prove2me | Definitions.Def_FewExperts_fewExpertsAlg
-- name    : FewExperts_fewExpertsAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:06.336581+00:00
-- url     : https://prove2.me/theorems/601629ea-97f2-4c9a-b2f8-6910f4f782d1
-- title:
--   Main and BoostAdvantage (Algorithm 4) with sampled play: the algorithm of Theorem 4
-- statement:
--   The algorithm of Theorem 4. Let $L_0=2^{25}\sqrt T\,r^2 s(s+\log r)\sqrt{\log(r+s)}$, $q=\alpha/(2^{10}r)$ and $m=\lceil 4r/q\rceil$.
--
--   1. **Main.** If $L_0\ge T$, it follows one expert for all $T$ rounds. Otherwise it runs epochs back to back, $\lceil 2^9rs/\alpha\rceil$ epochs at each of the $\lceil 2r\rceil$ scales $L=L_0,2L_0,4L_0,\dots$. It returns when the time is up. After the last epoch it follows a subscribed expert.
--   2. **BoostAdvantage$(t_0,L)$** (one epoch, started after round $t_0$). Set $\eta=8s/L$ and $\ell=L/(64rs)$. Let $\mathcal D(i)\propto\exp(-\eta a_{t_0}^i)$, where $a_t^i=L_0+G_t^{\mathrm{alg}}-G_t^i$ are the shifted advantages and $G^{\mathrm{alg}}$ is the algorithm's own mixed cumulative gain. Draw a multiset $I$ of $m$ independent samples from $\mathcal D$. Let $\mathcal B$ be Hedge with rate $\sqrt{\ln m/T}$ on the experts of $I$. Run HarvestGain$(\ell,T-t_0,\mathcal B)$ until it stops or the time runs out.
--   3. **Sampled play.** At each round the learner plays an expert drawn from Main's mixture, using a fresh uniform variable that nothing else reads.
--
--   The definition also records the regret and subscription rates of Theorem 4, the number of distinct experts played, the set of experts it subscribes to (the sampled experts of every epoch that runs, the transition experts of its HarvestGain run at every recursion depth, and the fallback expert), the potential $S=\mathrm{softmin}_{8s/L}(a)$, and two events. The sampling event says that in every epoch the best sampled expert is beaten by at most $q$ of $\mathcal D$'s mass. The stage conclusion says that the potential is at least $L/2$ at the end of every stopped run and above $2L$ after all runs of a scale stopped.
--
--   **Formalization Note** The algorithm is a `LimitedSwitching.HighProb.OnlineAlg`. At round $t$ it sees only its randomness and the gains of rounds $<t$. Its randomness is a family of independent uniform variables, one per label: the thresholds and samples of each epoch, and one variable per round for the play. All internal decisions use mixed gains, as on p.13. The paper omits the ceilings on $m$ and on the iteration counts, and they are added here. The fallback after the last epoch plays the first sampled expert of epoch $0$.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Algorithm 4 and §4.2, pp.19–22 (PDF pp.20–23); Theorem 4, p.15 (PDF p.16); §3.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
import Definitions.Def_FewExperts_softmin
import Definitions.Def_FewExperts_harvest

namespace FewExperts

open MeasureTheory

/-- `L₀ = 2²⁵ √T r² s(s + log r) √(log(r + s))` (§4.2, p.19, and Algorithm 4, line 10). -/
noncomputable def L0 (N T : ℕ) : ℝ :=
  2 ^ 25 * Real.sqrt T * rT T ^ 2 * sN N * (sN N + lg (rT T)) * Real.sqrt (lg (rT T + sN N))

/-- `q = α/(2¹⁰ r)` (p.19). -/
noncomputable def qParam (N T : ℕ) : ℝ := alpha N T / (2 ^ 10 * rT T)

/-- The sample size `m = ⌈4r/q⌉` (p.19; the paper omits the ceiling). -/
noncomputable def mParam (N T : ℕ) : ℕ := ⌈4 * rT T / qParam N T⌉₊

/-- The number `⌈2r⌉` of scales of Main (Algorithm 4, line 16; ceiling added). -/
noncomputable def nScales (T : ℕ) : ℕ := ⌈2 * rT T⌉₊

/-- The number `⌈2⁹ rs/α⌉` of epochs per scale (Algorithm 4, line 17; ceiling added). -/
noncomputable def nEpochs (N T : ℕ) : ℕ := ⌈2 ^ 9 * rT T * sN N / alpha N T⌉₊

/-- `η = 8s/L` (Algorithm 4, line 2). -/
noncomputable def etaOf (N : ℕ) (L : ℝ) : ℝ := 8 * sN N / L

/-- `ℓ = L/(64 r s)` (Algorithm 4, line 2). -/
noncomputable def ellOf (N T : ℕ) (L : ℝ) : ℝ := L / (64 * rT T * sN N)

/-- The scale `L = 2^c L₀` of epoch `k` (0-based), with `c = ⌊k / ⌈2⁹rs/α⌉⌋` the number of
doublings already made (Algorithm 4, lines 15–20). -/
noncomputable def scaleL (N T k : ℕ) : ℝ := 2 ^ (k / nEpochs N T) * L0 N T

/-- The labels of the independent uniform variables that drive the algorithm: for epoch `k`, the
threshold of expert `i` at recursion depth `d` (`thr k d i`) and the `j`-th sample (`samp k j`);
and the variable used to draw the expert played at round `t` (`play t`). -/
inductive RandIdx : Type
  | thr (k d i : ℕ)
  | samp (k j : ℕ)
  | play (t : ℕ)

/-- The randomness of the algorithm: one uniform variable on `[0, 1]` per label. -/
abbrev Rand : Type := RandIdx → unitInterval

/-- The law of the algorithm's randomness: the labels' uniform variables are independent. -/
noncomputable def fewExpertsLaw : Measure Rand :=
  Measure.infinitePi (fun _ : RandIdx => (volume : Measure unitInterval))

/-- The shifted advantage `a_t^i = L₀ + G_t^alg − G_t^i` (Algorithm 4, line 14; footnote 3,
p.19), given the algorithm's cumulative mixed gain `galg = G_t^alg`. -/
noncomputable def shiftedAdv {N : ℕ} (T : ℕ) (g : ℕ → Fin N → ℝ) (galg : ℝ) (t : ℕ)
    (i : Fin N) : ℝ :=
  L0 N T + galg - cumGain g t i

/-- The multiplicative-weights distribution `𝒟(i) ∝ exp(−η a^i)` ((13), p.19). -/
noncomputable def boostDist {N : ℕ} (η : ℝ) (a : Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.exp (-η * a i) / ∑ k, Real.exp (-η * a k)

/-- The distribution `𝒟` of epoch `k`, started after round `t0` with cumulative mixed gain
`galg` (Algorithm 4, line 3). -/
noncomputable def epochDist (N T k : ℕ) (g : ℕ → Fin N → ℝ) (t0 : ℕ) (galg : ℝ) : Fin N → ℝ :=
  boostDist (etaOf N (scaleL N T k)) (shiftedAdv T g galg t0)

/-- The multiset `I = (i₁, …, i_m)` of epoch `k`: `m` independent draws from `𝒟` (Algorithm 4,
line 4). -/
noncomputable def epochSamples (N T k : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) (t0 : ℕ)
    (galg : ℝ) : Fin (mParam N T) → Fin N :=
  fun j => sampleFin (epochDist N T k g t0 galg) (ω (RandIdx.samp k j.val))

/-- The baseline `B` of an epoch started after round `t0` (Algorithm 4, line 6): multiplicative
weights with rate `√(ln m / T)` on the experts of the multiset `I`. Its prediction at the run's
round `u` puts on expert `i` the total Hedge weight of the copies `j` with `I j = i`. -/
noncomputable def epochBaseline {N m : ℕ} (T : ℕ) (I : Fin m → Fin N) (g : ℕ → Fin N → ℝ)
    (t0 : ℕ) : ℕ → Fin N → ℝ :=
  fun u i => ∑ j ∈ Finset.univ.filter (fun j => I j = i),
    hedgeAt (hedgeRate m T) (fun j' v => g (t0 + v) (I j')) u j

/-- The run of HarvestGain(ℓ, T − t0, B) in epoch `k` (Algorithm 4, lines 2–8), with
`ℓ = L/(64rs)` for the epoch's scale `L`, its own fresh thresholds, and gains counted from the
epoch's start. -/
noncomputable def epochRun (N T k : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) (t0 : ℕ)
    (galg : ℝ) : HGRun N :=
  harvest N T (ellOf N T (scaleL N T k)) (T - t0)
    (epochBaseline T (epochSamples N T k ω g t0 galg) g t0) (fun u => g (t0 + u))
    (fun d i => ω (RandIdx.thr k d i.val))

/-- The state of Main before epoch `k` (0-based): the number `t0` of rounds already played and
the cumulative mixed gain `G_{t0}^alg`. Epoch `k` runs only while `k < ⌈2r⌉ · ⌈2⁹rs/α⌉` and
`t0 < T` (line 18: "return if t0 = T"); it lasts until its HarvestGain run stops, or until round
`T` (line 8). -/
noncomputable def epochState (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) : ℕ → ℕ × ℝ
  | 0 => (0, 0)
  | k + 1 =>
    let st := epochState N T ω g k
    if k < nScales T * nEpochs N T ∧ st.1 < T then
      let A := epochRun N T k ω g st.1 st.2
      let len := min (A.stopOrEnd (T - st.1)) (T - st.1)
      (st.1 + len, st.2 + cumMix (fun u => g (st.1 + u)) A.pred len)
    else st

open Classical in
/-- **Main** (Algorithm 4, p.20): its mixed prediction at round `t ∈ {1, …, T}`.
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Algorithm 4, p.20 (PDF 21).

* If `L₀ ≥ T`, follow expert `0` for all `T` rounds (lines 11–12).
* Otherwise, round `t` belongs to the first epoch `k < ⌈2r⌉⌈2⁹rs/α⌉` whose end is `≥ t`, and the
  prediction is that of the epoch's HarvestGain run at its own round `t − t0`.
* After all epochs, follow the first sampled expert of epoch `0`, which is subscribed (line 21).

**Formalization Note** All internal decisions (the distributions `𝒟`, the stopping tests) use
mixed gains, as the paper prescribes (p.13: "Subscription and stopping decisions use the mixed
gains"). -/
noncomputable def mainMix (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) (t : ℕ) :
    Fin N → ℝ :=
  if (T : ℝ) ≤ L0 N T then fun i => if i = 0 then 1 else 0
  else if hk : ∃ k, k < nScales T * nEpochs N T ∧ t ≤ (epochState N T ω g (k + 1)).1 then
    (epochRun N T (Nat.find hk) ω g (epochState N T ω g (Nat.find hk)).1
      (epochState N T ω g (Nat.find hk)).2).pred (t - (epochState N T ω g (Nat.find hk)).1)
  else if hm : 0 < mParam N T then
    fun i => if i = epochSamples N T 0 ω g 0 0 ⟨0, hm⟩ then 1 else 0
  else fun i => if i = 0 then 1 else 0

/-- The mixture Main uses at round `t`, computed from the gains of rounds `1, …, t − 1` only (the
gains of rounds `≥ t` are replaced by `0`; Main never reads them). -/
noncomputable def fewExpertsMix (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) (t : ℕ) :
    Fin N → ℝ :=
  mainMix N T ω (LimitedSwitching.HighProb.padPast (fun s : Fin (t - 1) => g (s.val + 1))) t

/-- **The algorithm of Theorem 4** (Algorithms 3 and 4 with sampled predictions).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 4, p.15 (PDF 16), Algorithms 3–4, pp.16, 20, and §3.1, p.13.

A randomized online algorithm (`LimitedSwitching.HighProb.OnlineAlg`: at round `t` it sees only
its randomness and the gains of rounds `1, …, t − 1`): at round `t` it plays the expert drawn
from Main's mixture `fewExpertsMix` with the round's own uniform variable `ω (play t)`.

**Formalization Note** The sampling device is `sampleFin` (inverse CDF), fed with a uniform
variable that nothing else reads, so the played experts are drawn independently of all internal
randomness, given the mixtures. -/
noncomputable def fewExpertsAlg (N T : ℕ) [NeZero N] : LimitedSwitching.HighProb.OnlineAlg Rand N :=
  fun ω t past =>
    sampleFin (mainMix N T ω (LimitedSwitching.HighProb.padPast past) t) (ω (RandIdx.play t))

/-- The expert played at round `t` by the algorithm of Theorem 4 against the gains `g`. -/
noncomputable def fewExpertsPlay (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) :
    ℕ → Fin N :=
  LimitedSwitching.HighProb.play (fewExpertsAlg N T) ω g

/-- The number of distinct experts played in rounds `1, …, T`. -/
noncomputable def playedCount (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) : ℕ :=
  ((Finset.Icc 1 T).image (fewExpertsPlay N T ω g)).card

open Classical in
/-- **The experts the algorithm of Theorem 4 subscribes to** (Algorithm 4, lines 5, 12, 21, and
Algorithm 3, line 14; §4.2, p.22: "Each run of BoostAdvantage subscribes to at most m sampled
experts, and the corresponding run of HarvestGain subscribes to at most log T additional
experts").

* If `L₀ ≥ T`: the one expert it follows (expert `0`, line 12).
* Otherwise: for every epoch that runs (`k < ⌈2r⌉⌈2⁹rs/α⌉` and `t0 < T`), the sampled multiset
  `I` of the epoch (line 5) and the transition experts `i*` of its HarvestGain run at all
  recursion depths (`HGRun.subs`, line 14 of Algorithm 3); and the fallback expert of line 21
  (the first sample of epoch `0`, expert `0` if `m = 0`).

**Formalization Note** `HGRun.subs` collects the transition experts of every recursion depth,
including a transition of a recursive run `A′` that would come after the outer run already
stopped, so this set contains the experts actually subscribed to (it may be larger). -/
noncomputable def subscribedSet (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) :
    Finset (Fin N) :=
  if (T : ℝ) ≤ L0 N T then {0}
  else
    (if hm : 0 < mParam N T then {epochSamples N T 0 ω g 0 0 ⟨0, hm⟩} else {0}) ∪
      ((Finset.range (nScales T * nEpochs N T)).filter
          (fun k => (epochState N T ω g k).1 < T)).biUnion
        (fun k =>
          Finset.univ.image
              (epochSamples N T k ω g (epochState N T ω g k).1 (epochState N T ω g k).2) ∪
            (epochRun N T k ω g (epochState N T ω g k).1 (epochState N T ω g k).2).subs)

/-- The regret rate of Theorem 4,
`√T log²T log N (log N + log log T) √(log log T + log log N)` (logs base 2). -/
noncomputable def regretRate (N T : ℕ) : ℝ :=
  Real.sqrt T * lg T ^ 2 * lg N * (lg N + lg (lg T)) * Real.sqrt (lg (lg T) + lg (lg N))

/-- The subscription rate of Theorem 4, `log⁶T log N (log N + log log T)²` (logs base 2). -/
noncomputable def subsRate (N T : ℕ) : ℝ :=
  lg T ^ 6 * lg N * (lg N + lg (lg T)) ^ 2

open Classical in
/-- The `𝒟`-mass of the experts that beat every expert of the multiset `I` on the score `x`
("the best expert in I is … beaten by at most q mass of experts (where mass is measured under
𝒟)", p.20): `∑ {𝒟(i) : x_i > max_{j} x_{I_j}}`. -/
noncomputable def beatenMass {N m : ℕ} (D : Fin N → ℝ) (x : Fin N → ℝ) (I : Fin m → Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ∀ j, x (I j) < x i), D i

/-- The sampling event of §4.2 (p.20): in every epoch that runs, at every time `t` after its
start `t0`, the best sampled expert on the interval gains `G^i_{(t0,t]}` is beaten by at most `q`
of `𝒟`'s mass. -/
def SampOK (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) : Prop :=
  ∀ k < nScales T * nEpochs N T, (epochState N T ω g k).1 < T →
    ∀ t, (epochState N T ω g k).1 < t → t ≤ T →
      beatenMass (epochDist N T k g (epochState N T ω g k).1 (epochState N T ω g k).2)
        (fun i => cumGain g t i - cumGain g (epochState N T ω g k).1 i)
        (epochSamples N T k ω g (epochState N T ω g k).1 (epochState N T ω g k).2)
        ≤ qParam N T

/-- The potential `S_{t0} = softmin_η(a_{t0})` with `η = 8s/L` ((14), p.19), at the state
`st = (t0, G_{t0}^alg)`. -/
noncomputable def potentialAt (N T : ℕ) (L : ℝ) (g : ℕ → Fin N → ℝ) (st : ℕ × ℝ) : ℝ :=
  softmin (etaOf N L) (shiftedAdv T g st.2 st.1)

/-- The conclusion of the stage concentration argument (p.22): at the end of every stopped run the
potential (at the run's scale `L`) is at least `L/2` ("never go below L/2"), and after all
`⌈2⁹rs/α⌉` runs of a scale `L = 2^c L₀` have run and stopped, the potential is above `2L`
("go above 2L"). -/
def StageGood (N T : ℕ) [NeZero N] (ω : Rand) (g : ℕ → Fin N → ℝ) : Prop :=
  (∀ k < nScales T * nEpochs N T, (epochState N T ω g k).1 < T →
      (epochRun N T k ω g (epochState N T ω g k).1 (epochState N T ω g k).2).stop.isSome →
        scaleL N T k / 2 ≤ potentialAt N T (scaleL N T k) g (epochState N T ω g (k + 1))) ∧
  (∀ c < nScales T,
      (∀ k, c * nEpochs N T ≤ k → k < (c + 1) * nEpochs N T →
        (epochState N T ω g k).1 < T ∧
          (epochRun N T k ω g (epochState N T ω g k).1 (epochState N T ω g k).2).stop.isSome) →
        2 * (2 ^ c * L0 N T) <
          potentialAt N T (2 ^ c * L0 N T) g (epochState N T ω g ((c + 1) * nEpochs N T)))

end FewExperts


