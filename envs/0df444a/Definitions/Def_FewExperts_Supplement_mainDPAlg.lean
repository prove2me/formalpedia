-- Prove2me | Definitions.Def_FewExperts_Supplement_mainDPAlg
-- name    : FewExperts_Supplement_mainDPAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:54:24.1982+00:00
-- url     : https://prove2.me/theorems/c5918b73-2ac3-4010-90ac-f5c4972f8d3f
-- title:
--   MainDP (Algorithm 6): the $\varepsilon$-differentially private main algorithm and its parameters
-- statement:
--   Let $r=\log T$ and $s=\log N$, and let $\alpha$, $q$ and $m=\lceil4r/q\rceil$ be as in the non-private algorithm. For $0<\varepsilon\le1$ set
--
--   $$L_0=2^{77}\Bigl(\sqrt T\,r^2s(s+\log r)\sqrt{\log(r+s)}+\frac{r^9s^2(s+\log r)^3\log(r+s)}{\varepsilon}\Bigr),\qquad n_{\mathrm{epochs}}=\frac{2^{12}r^2s}{\alpha},$$
--
--   and, for a scale $L$,
--
--   $$\varepsilon_{\mathrm H}=\frac{\varepsilon rL_0}{6n_{\mathrm{epochs}}mL},\qquad\varepsilon_{\mathrm A}=\frac{\varepsilon L_0}{24n_{\mathrm{epochs}}L},\qquad\varepsilon_{\mathrm{sv}}=\frac{\varepsilon L_0}{12n_{\mathrm{epochs}}L}.$$
--
--   **MainDP** works as follows.
--
--   1. If $L_0\ge T$, it follows one fixed expert.
--   2. Otherwise, starting from $L=L_0$, it runs $\lceil2r\rceil$ scales, doubling $L$ after each. Each scale has $\lceil2^{11}rs/\alpha\rceil$ epochs, and the whole loop returns as soon as round $T$ is reached.
--   3. An epoch starting after round $t_0$ is a run of **BoostAdvantageDP**$(t_0,L)$:
--      - set $\eta=8s/L$ and $\ell=L/(64rs)$;
--      - sample a multiset $I$ of $m$ experts independently from $\mathcal D(i)\propto\exp(-\eta a^i_{t_0})$ and subscribe to them;
--      - set $G^*_t=\max_{j\in I}G^j_{(t_0,t]}$;
--      - let $\mathcal B$ be private Hedge on the experts of $I$ with horizon $T$ and parameter $\varepsilon_{\mathrm H}$;
--      - run HarvestGainDP$(\ell,T-t_0,G^*,\mathcal B)$ until it stops or the time runs out.
--   4. After all epochs, it follows the first subscribed expert.
--
--   At each round the algorithm plays an expert sampled from its current mixture. This is the algorithm of Theorem 5.
--
--   **Formalization Note** The shifted advantage is $a^i_{t_0}=\mathbb E_{\mathcal S}[G^{\mathrm{alg}}_{t_0}]-G^i_{t_0}+L_0$. Its $i$-independent part cancels in the normalization, so $\mathcal D(i)=\exp(\eta G^i_{t_0})/\sum_k\exp(\eta G^k_{t_0})$, and it is computed in that form. Here $\mathcal S$ is the randomness of the private Hedge instances; the algorithm itself never uses $\mathbb E_{\mathcal S}$. The randomness is a family of independent uniform variables indexed by `RandIdxDP`: samples, the HarvestGainDP variables, the baseline trees and one variable per round for the play. The fixed expert is expert $0$, and the first subscribed expert is the first sample of epoch $0$. The floors and ceilings omitted by the paper are written explicitly. The maximum over $I$ is `⨆`, which equals the maximum for $m\ge1$. The rate `rateDP` is the expression of Theorem 5.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §5.2, Algorithm 6, p.30 (PDF p.31), (27), p.28 (PDF p.29), (28), p.29 (PDF p.30)

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg
import Definitions.Def_FewExperts_Supplement_harvestDP

namespace FewExperts.Supplement

open MeasureTheory

/-- `L₀ = 2⁷⁷ (√T r² s (s + log r) √(log(r + s)) + r⁹ s² (s + log r)³ log(r + s) / ε)` ((27), p.28),
logs base 2. -/
noncomputable def L0DP (N T : ℕ) (ε : ℝ) : ℝ :=
  2 ^ 77 * (Real.sqrt T * rT T ^ 2 * sN N * (sN N + lg (rT T)) * Real.sqrt (lg (rT T + sN N)) +
    rT T ^ 9 * sN N ^ 2 * (sN N + lg (rT T)) ^ 3 * lg (rT T + sN N) / ε)

/-- `n_epochs = 2¹² r² s / α` (p.28), the bound on the number of epochs used in (28). -/
noncomputable def nEpochsDP (N T : ℕ) : ℝ := 2 ^ 12 * rT T ^ 2 * sN N / alpha N T

/-- The number `⌈2¹¹ rs/α⌉` of epochs per value of `L` (Algorithm 6, line 18; ceiling added). -/
noncomputable def epochsPerScaleDP (N T : ℕ) : ℕ := ⌈2 ^ 11 * rT T * sN N / alpha N T⌉₊

/-- The scale `L = 2^c L₀` of epoch `k` (0-based), `c = ⌊k / ⌈2¹¹rs/α⌉⌋` (Algorithm 6, lines
16–21). -/
noncomputable def scaleLDP (N T : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  2 ^ (k / epochsPerScaleDP N T) * L0DP N T ε

/-- `ε_H = ε r L₀ / (6 n_epochs m L)` ((28), p.29). -/
noncomputable def epsH (N T : ℕ) (ε L : ℝ) : ℝ :=
  ε * rT T * L0DP N T ε / (6 * nEpochsDP N T * mParam N T * L)

/-- `ε_A = ε L₀ / (24 n_epochs L)` ((28), p.29). -/
noncomputable def epsA (N T : ℕ) (ε L : ℝ) : ℝ := ε * L0DP N T ε / (24 * nEpochsDP N T * L)

/-- `ε_sv = ε L₀ / (12 n_epochs L)` ((28), p.29). -/
noncomputable def epsSv (N T : ℕ) (ε L : ℝ) : ℝ := ε * L0DP N T ε / (12 * nEpochsDP N T * L)

/-- The labels of the independent uniform variables that drive MainDP: for epoch `k`, the `j`-th
sample (`samp k j`), the variables of its HarvestGainDP run (`harv k x`), and the tree of copy `j`
of the sampled baseline `B` (`bNode k j lvl idx`, `bPad k j t lvl`); and the variable used to draw
the expert played at round `t` (`play t`). The trees (`bNode`, `bPad`, and the `node`, `pad` labels
inside `harv`) form the randomness `S` of §5 (p.23); `samp`, the other `harv` labels and `play` form
`R`. -/
inductive RandIdxDP : Type
  | samp (k j : ℕ)
  | harv (k : ℕ) (x : HIdx)
  | bNode (k j lvl idx : ℕ)
  | bPad (k j t lvl : ℕ)
  | play (t : ℕ)

/-- The randomness of MainDP: one uniform variable on `[0, 1]` per label. -/
abbrev RandDP : Type := RandIdxDP → unitInterval

/-- The law of MainDP's randomness: the labels' uniform variables are independent. -/
noncomputable def lawDP : Measure RandDP :=
  Measure.infinitePi (fun _ : RandIdxDP => (volume : Measure unitInterval))

/-- The distribution `𝒟` of epoch `k`, started after round `t0` (Algorithm 6, line 4):
`𝒟(i) ∝ exp(−η a^i_{t0})` with `η = 8s/L` and `a^i_{t0} = E_S[G^alg_{t0}] − G^i_{t0} + L₀`.

**Formalization Note** The term `E_S[G^alg_{t0}] + L₀` does not depend on `i` and cancels in the
normalization, so `𝒟(i) = exp(η G^i_{t0}) / ∑_k exp(η G^k_{t0})` (as §5.3, p.32, notes: "Up to a
factor common to every expert, 𝒟(i) ∝ exp(ηG^i_{t0})"); it is computed in this form. -/
noncomputable def epochDistDP (N T : ℕ) (ε : ℝ) (k : ℕ) (g : ℕ → Fin N → ℝ) (t0 : ℕ) :
    Fin N → ℝ :=
  boostDist (etaOf N (scaleLDP N T ε k)) (fun i => -cumGain g t0 i)

/-- The multiset `I = (i₁, …, i_m)` of epoch `k`: `m` independent draws from `𝒟` (Algorithm 6,
line 5). -/
noncomputable def epochSamplesDP (N T : ℕ) [NeZero N] (ε : ℝ) (k : ℕ) (ω : RandDP)
    (g : ℕ → Fin N → ℝ) (t0 : ℕ) : Fin (mParam N T) → Fin N :=
  fun j => sampleFin (epochDistDP N T ε k g t0) (ω (RandIdxDP.samp k j.val))

/-- The baseline gain function `G*_t = max_{j ∈ I} G^j_{(t0, t0+t]}` of an epoch started after round
`t0` (Algorithm 6, line 7), at the run's round `t`.

**Formalization Note** The maximum over `Fin m` is `⨆`; it is the true maximum for `m ≥ 1`. -/
noncomputable def gStarDP {N m : ℕ} (I : Fin m → Fin N) (g : ℕ → Fin N → ℝ) (t0 : ℕ) : ℕ → ℝ :=
  fun t => ⨆ j, (cumGain g (t0 + t) (I j) - cumGain g t0 (I j))

/-- The sampled baseline `B` of epoch `k` started after round `t0` (Algorithm 6, line 8): private
multiplicative weights (`privHedgeAt`, Lemma 4) on the `m` experts of the multiset `I`, horizon `T`,
scalar-tree parameter `ε_H`, one tree per copy. Its prediction at the run's round `u` puts on
expert `i` the total weight of the copies `j` with `I j = i`. -/
noncomputable def baselineDP {N m : ℕ} (T k : ℕ) (εH : ℝ) (ω : RandDP) (I : Fin m → Fin N)
    (g : ℕ → Fin N → ℝ) (t0 : ℕ) : ℕ → Fin N → ℝ :=
  fun u i => ∑ j ∈ Finset.univ.filter (fun j => I j = i),
    privHedgeAt T εH (fun j' v => g (t0 + v) (I j'))
      (fun j' lvl idx => ω (RandIdxDP.bNode k j'.val lvl idx))
      (fun j' t lvl => ω (RandIdxDP.bPad k j'.val t lvl)) u j

/-- The run of BoostAdvantageDP(t0, L) in epoch `k` (Algorithm 6, lines 1–10): with `L` the
epoch's scale, `ℓ = L/(64rs)`, the parameters `ε_H, ε_A, ε_sv` of (28), the samples `I`, `G*` and
`B`, the run of HarvestGainDP(ℓ, T − t0, G*, B) on the gains counted from the epoch's start, with
the epoch's own fresh variables. -/
noncomputable def epochRunDP (N T : ℕ) [NeZero N] (ε : ℝ) (k : ℕ) (ω : RandDP)
    (g : ℕ → Fin N → ℝ) (t0 : ℕ) : HGRun N :=
  harvestDP N T (ellOf N T (scaleLDP N T ε k)) (epsA N T ε (scaleLDP N T ε k))
    (epsSv N T ε (scaleLDP N T ε k)) (T - t0) (gStarDP (epochSamplesDP N T ε k ω g t0) g t0)
    (baselineDP T k (epsH N T ε (scaleLDP N T ε k)) ω (epochSamplesDP N T ε k ω g t0) g t0)
    (fun u => g (t0 + u)) (fun x => ω (RandIdxDP.harv k x))

/-- The number `t0` of rounds MainDP has played before epoch `k` (0-based). Epoch `k` runs only
while `k < ⌈2r⌉ · ⌈2¹¹rs/α⌉` and `t0 < T` (line 19: "return if t0 = T"); it lasts until its
HarvestGainDP run stops, or until round `T` (line 10). -/
noncomputable def epochStartDP (N T : ℕ) [NeZero N] (ε : ℝ) (ω : RandDP) (g : ℕ → Fin N → ℝ) :
    ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let st := epochStartDP N T ε ω g k
    if k < nScales T * epochsPerScaleDP N T ∧ st < T then
      st + min ((epochRunDP N T ε k ω g st).stopOrEnd (T - st)) (T - st)
    else st

open Classical in
/-- **MainDP** (Algorithm 6, p.30): its mixed prediction at round `t ∈ {1, …, T}`.
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Algorithm 6, p.30 (PDF 31).

* If `L₀ ≥ T` (with `L₀` of (27)), follow expert `0` for all `T` rounds (lines 13–14).
* Otherwise, round `t` belongs to the first epoch `k < ⌈2r⌉⌈2¹¹rs/α⌉` whose end is `≥ t`, and the
  prediction is that of the epoch's HarvestGainDP run at its own round `t − t0`.
* After all epochs, follow the first sampled expert of epoch `0`, the first subscribed expert
  (line 22). -/
noncomputable def mainDPMix (N T : ℕ) [NeZero N] (ε : ℝ) (ω : RandDP) (g : ℕ → Fin N → ℝ)
    (t : ℕ) : Fin N → ℝ :=
  if (T : ℝ) ≤ L0DP N T ε then fun i => if i = 0 then 1 else 0
  else if hk : ∃ k, k < nScales T * epochsPerScaleDP N T ∧ t ≤ epochStartDP N T ε ω g (k + 1) then
    (epochRunDP N T ε (Nat.find hk) ω g (epochStartDP N T ε ω g (Nat.find hk))).pred
      (t - epochStartDP N T ε ω g (Nat.find hk))
  else if hm : 0 < mParam N T then
    fun i => if i = epochSamplesDP N T ε 0 ω g 0 ⟨0, hm⟩ then 1 else 0
  else fun i => if i = 0 then 1 else 0

/-- **The ε-DP algorithm of Theorem 5** (Algorithms 5 and 6 with sampled predictions).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 5, p.23 (PDF 24), Algorithms 5–6, pp.25, 30, and §3.1, p.13.

A randomized online algorithm (`LimitedSwitching.HighProb.OnlineAlg`: at round `t` it sees only its
randomness and the gains of rounds `1, …, t − 1`): at round `t` it plays the expert drawn from
MainDP's mixture `mainDPMix` (computed from the past gains, later rounds set to `0`) with the round's
own uniform variable `ω (play t)`.

**Formalization Note** The sampling device is `sampleFin` (inverse CDF). The Laplace variables are
inverse-CDF transforms (`lapInv`) of the uniform variables. The paper only cites the mechanisms of
Lemmas 3–5; their pinned instances are `treeNoise`, `privHedgeAt` and `svFires`. -/
noncomputable def mainDPAlg (N T : ℕ) [NeZero N] (ε : ℝ) :
    LimitedSwitching.HighProb.OnlineAlg RandDP N :=
  fun ω t past =>
    sampleFin (mainDPMix N T ε ω (LimitedSwitching.HighProb.padPast past) t)
      (ω (RandIdxDP.play t))

/-- The expert played at round `t` by MainDP against the gains `g`. -/
noncomputable def playDP (N T : ℕ) [NeZero N] (ε : ℝ) (ω : RandDP) (g : ℕ → Fin N → ℝ) :
    ℕ → Fin N :=
  LimitedSwitching.HighProb.play (mainDPAlg N T ε) ω g

/-- The regret rate of Theorem 5 (logs base 2):
`√T log²T log N (log N + log log T) √(log log T + log log N)
  + log⁹T log²N (log N + log log T)³ (log log T + log log N) / ε`. -/
noncomputable def rateDP (N T : ℕ) (ε : ℝ) : ℝ :=
  regretRate N T +
    lg T ^ 9 * lg N ^ 2 * (lg N + lg (lg T)) ^ 3 * (lg (lg T) + lg (lg N)) / ε

end FewExperts.Supplement


