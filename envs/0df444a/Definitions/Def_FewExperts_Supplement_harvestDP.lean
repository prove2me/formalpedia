-- Prove2me | Definitions.Def_FewExperts_Supplement_harvestDP
-- name    : FewExperts_Supplement_harvestDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:53:04.626206+00:00
-- url     : https://prove2.me/theorems/4a53789f-250e-4f95-bef1-b9cd2987b2ef
-- title:
--   HarvestGainDP (Algorithm 5): the private gain-harvesting subroutine
-- statement:
--   **HarvestGainDP**$(\ell,\widetilde T,G^*,\mathcal B)$ (Algorithm 5) runs for $\widetilde T$ rounds. Its inputs are a parameter $\ell$, a baseline gain function $G^*_t$ with $G^*_0=0$, and a baseline algorithm $\mathcal B$. It also uses privacy parameters $\varepsilon_{\mathrm A}$ (for trees) and $\varepsilon_{\mathrm{sv}}$ (for sparse vector). Gains $G^i_t$ are counted from the start of the run, and $\alpha$, $p$, $K=\lfloor1/\alpha\rfloor$ are the published constants.
--
--   1. If $\widetilde T=1$, follow $\mathcal B$ for one round and do not stop.
--   2. Otherwise, draw thresholds $r_i\in\{1,\dots,K\}$ independently with $\Pr[r_i\le j]=p^{K-j}$, and start a sparse-vector instance $\mathrm{SV}_{\mathrm{tr}}$ with sensitivity $4$. Follow $\mathcal B$. After each round $t<\widetilde T$, query $\mathrm{SV}_{\mathrm{tr}}$ for $i=1,\dots,N$ in order with
--   $$G^i_t-G^*_t-r_i\alpha\ell\ge\alpha\ell/8 .$$
--   If no query is ever answered true, the run ends after $\widetilde T$ rounds without stopping.
--   3. At the first true answer, for expert $i^*$ at round $t^*$, set $r^*=r_{i^*}$ and subscribe to $i^*$. Set $\widetilde T'=\min(\lfloor\widetilde T/2\rfloor,\widetilde T-t^*)$ and $H^*_s=G^*_{t^*+s}-G^*_{t^*}$. Let $\mathcal B'$ be the two-expert private Hedge on $\mathcal B$ and $i^*$, with horizon $\widetilde T'$ and parameter $\varepsilon_{\mathrm A}$ (take $\mathcal B'=\mathcal B$ if $\widetilde T'=1$). On the next $\widetilde T'$ rounds, follow the recursive run $\mathcal A'=$ HarvestGainDP$(\ell,\widetilde T',H^*,\mathcal B')$, which uses fresh randomness.
--   4. In this second phase, stop at the first round $t\in\{t^*+1,\dots,t^*+\widetilde T'\}$ at which any of the following holds:
--      - $\mathcal A'$ stops;
--      - a fresh sparse-vector instance $\mathrm{SV}_{\mathrm{stop}}$ (sensitivity $4$) answers true to $G^{i^*}_t-G^*_t-r^*\alpha\ell\ge 7\alpha\ell/8$;
--      - $t=t^*+\widetilde T'$.
--
--   The record of a run is its mixed prediction at each round, its stopping round (if any) and the set of experts it subscribes to. This is the building block of each epoch of MainDP.
--
--   **Formalization Note** Rounds are 1-based and relative to the start of the run. The run's randomness is a family of uniform variables indexed by `HIdx`. Depth $d$ of a recursive run is depth $d+1$ of its caller. The transitions and stopping rounds depend only on the gains, on $G^*$, on the thresholds and on the sparse-vector noise (the randomness $\mathcal R$ of §5). They never depend on $\mathcal B$'s predictions or on the Hedge trees ($\mathcal S$). The record type `HGRun` and the helpers `level`, `firstFin`, `phase2Horizon`, `pairStreams` and `phase2Stop` are the published ones of HarvestGain.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §5.1, Algorithm 5, p.25 (PDF p.26), and proof of Proposition 3, pp.24–26 (PDF pp.25–27)

import Mathlib
import Definitions.Def_FewExperts_harvest
import Definitions.Def_FewExperts_Supplement_privHedgeAt

namespace FewExperts.Supplement

/-- The labels of the uniform variables that drive one run of HarvestGainDP and its recursive runs
(depth `d = 0` for the run itself, `d ≥ 1` for the recursive runs):
* `thr d i`: the threshold index `r_i` of expert `i` (Algorithm 5, line 5);
* `trRho d`, `trNu d t i`: the noises of the transition mechanism `SV_tr` (line 6, 13): `ρ` once,
  `ν` for the query on expert `i` after round `t`;
* `stRho d`, `stNu d u`: the noises of the stopping mechanism `SV_stop` (lines 21, 28), `ν` for the
  query at the second-phase round `u`;
* `node d j k idx`, `pad d j t k`: the tree of stream `j ∈ {0, 1}` of the two-expert private Hedge
  `B′` (line 18).

The first three kinds are part of the randomness `R` of §5 (p.23); the tree variables are part of
`S`, which only drives predictions. -/
inductive HIdx : Type
  | thr (d i : ℕ)
  | trRho (d : ℕ)
  | trNu (d t i : ℕ)
  | stRho (d : ℕ)
  | stNu (d u : ℕ)
  | node (d j k idx : ℕ)
  | pad (d j t k : ℕ)

/-- The labels of the recursive run: depth `d` of the recursive run is depth `d + 1` of the caller
(fresh randomness for every recursive call). -/
def HIdx.shift : HIdx → HIdx
  | .thr d i => .thr (d + 1) i
  | .trRho d => .trRho (d + 1)
  | .trNu d t i => .trNu (d + 1) t i
  | .stRho d => .stRho (d + 1)
  | .stNu d u => .stNu (d + 1) u
  | .node d j k idx => .node (d + 1) j k idx
  | .pad d j t k => .pad (d + 1) j t k

open Classical in
/-- **The transition of HarvestGainDP** (Algorithm 5, lines 5–15, and (23), p.24): the first round
`t* ∈ {1, …, T̃ − 1}` and, at that round, the first expert `i*` (querying `i = 1, …, N` in order) on
which `SV_tr` answers true to the query `G_t^i − G*_t − r_i α ℓ ≥ α ℓ / 8` (sensitivity `4`, privacy
parameter `ε_sv`), with `r* = r_{i*}`. `none` if `SV_tr` never answers true. Gains `h` and the
baseline gain function `G*` are counted from the start of the run. -/
noncomputable def transDP (N T : ℕ) (ℓ εsv : ℝ) (Ttil : ℕ) (Gs : ℕ → ℝ) (h : ℕ → Fin N → ℝ)
    (τ : HIdx → unitInterval) : Option (ℕ × Fin N × ℕ) :=
  if hex : ∃ t, 1 ≤ t ∧ t < Ttil ∧ ∃ i : Fin N,
      svFires εsv 4 (τ (.trRho 0)) (τ (.trNu 0 t i.val))
        (cumGain h t i - Gs t - (level N T (τ (.thr 0 i.val)) : ℝ) * alpha N T * ℓ)
        (alpha N T * ℓ / 8) then
    let i := firstFin (fun i : Fin N =>
        svFires εsv 4 (τ (.trRho 0)) (τ (.trNu 0 (Nat.find hex) i.val))
          (cumGain h (Nat.find hex) i - Gs (Nat.find hex) -
            (level N T (τ (.thr 0 i.val)) : ℝ) * alpha N T * ℓ)
          (alpha N T * ℓ / 8)) (Nat.find_spec hex).2.2
    some (Nat.find hex, i, level N T (τ (.thr 0 i.val)))
  else none

/-- **The baseline `B′` of the second phase of HarvestGainDP** (Algorithm 5, line 18; p.24: "Let B′
be the two-expert private Hedge algorithm from Lemma 4, run on B and i*, started at time t* and run
with scalar-tree privacy parameter ε_A for at most T̃′ time steps"). Its prediction at its own round
`u ≥ 1` (run round `t* + u`) is `w_u · B_{t*+u} + (1 − w_u) · δ_{i*}`, where `(w_u, 1 − w_u)` is
private Hedge (`privHedgeAt`, horizon `T̃′`, parameter `ε_A`) on the two gain streams of
`pairStreams` (the mixed gain of `B` and the gain of `i*`), with the trees of depth `0` of `τ`. -/
noncomputable def privPairPred {N : ℕ} (b h : ℕ → Fin N → ℝ) (ts : ℕ) (is : Fin N) (T' : ℕ)
    (εA : ℝ) (τ : HIdx → unitInterval) : ℕ → Fin N → ℝ :=
  fun u i =>
    privHedgeAt T' εA (pairStreams b h ts is) (fun j k idx => τ (.node 0 j.val k idx))
        (fun j t k => τ (.pad 0 j.val t k)) u 0 * b (ts + u) i +
      privHedgeAt T' εA (pairStreams b h ts is) (fun j k idx => τ (.node 0 j.val k idx))
        (fun j t k => τ (.pad 0 j.val t k)) u 1 * (if i = is then 1 else 0)

open Classical in
/-- **HarvestGainDP(ℓ, T̃, G*, B)** (Algorithm 5, p.25, and the proof of Proposition 3, pp.24–26).
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Algorithm 5, p.25 (PDF 26).

`harvestDP N T ℓ ε_A ε_sv T̃ G* b h τ` is the run with parameter `ℓ`, horizon `T̃`, baseline gain
function `G*_u` (`u` a round of the run, `G*_0 = 0`), a baseline `B` with (mixed) predictions `b u`
at the run's rounds `u = 1, …, T̃`, gains `h u i` at the run's rounds, and the labelled uniform
variables `τ` (depth `0` for this run, depths `≥ 1` for the recursive runs).

* If `T̃ ≤ 1`, follow `B` and do not stop (lines 2–4).
* Otherwise, follow `B` until the transition `(t*, i*, r*) = transDP …` (lines 7–15); if there is
  none, follow `B` until `T̃` and do not stop. If there is one, subscribe to `i*`, set
  `T̃′ = min(⌊T̃/2⌋, T̃ − t*)` and `H*_s = G*_{(t*, t*+s]}`, let `B′` be the two-expert private Hedge
  on `B` and `i*` with parameter `ε_A` (`B′ = B` if `T̃′ = 1`), and follow the recursive run
  `A′ = HarvestGainDP(ℓ, T̃′, H*, B′)` on the next rounds (lines 16–22).
* In the second phase, stop at the first round `t ∈ {t* + 1, …, t* + T̃′}` at which `A′` stops, or
  `SV_stop` (sensitivity `4`, parameter `ε_sv`) answers true to
  `G_t^{i*} − G*_t − r* α ℓ ≥ 7 α ℓ / 8`, or `t = t* + T̃′` (lines 24–30).

**Formalization Note** Rounds are 1-based and relative to the start of the run. The prediction is
defined at every round; after the second phase it is set to `B`'s (never read: the run has
stopped). The transition and the stopping round depend only on the gains, `G*` and the variables
`thr`, `trRho`, `trNu`, `stRho`, `stNu` (the randomness `R`), never on `B`'s predictions or on the
trees (`S`), as §5 requires (p.23). The record type `HGRun` is the published one of HarvestGain. -/
noncomputable def harvestDP (N T : ℕ) (ℓ εA εsv : ℝ) (Ttil : ℕ) (Gs : ℕ → ℝ)
    (b h : ℕ → Fin N → ℝ) (τ : HIdx → unitInterval) : HGRun N :=
  if _hT : Ttil ≤ 1 then ⟨b, none, ∅⟩
  else
    match transDP N T ℓ εsv Ttil Gs h τ with
    | none => ⟨b, none, ∅⟩
    | some (ts, is, rs) =>
      let A' := harvestDP N T ℓ εA εsv (phase2Horizon Ttil ts) (fun s => Gs (ts + s) - Gs ts)
        (if phase2Horizon Ttil ts = 1 then fun u => b (ts + u)
          else privPairPred b h ts is (phase2Horizon Ttil ts) εA τ)
        (fun u => h (ts + u)) (fun x => τ x.shift)
      { pred := fun u => if u ≤ ts then b u
          else if u ≤ ts + phase2Horizon Ttil ts then A'.pred (u - ts) else b u
        stop := (phase2Stop (phase2Horizon Ttil ts) A'.stop
          (fun u => svFires εsv 4 (τ (.stRho 0)) (τ (.stNu 0 u))
            (cumGain h (ts + u) is - Gs (ts + u) - (rs : ℝ) * alpha N T * ℓ)
            (7 * alpha N T * ℓ / 8))).map (ts + ·)
        subs := insert is A'.subs }
termination_by Ttil
decreasing_by unfold phase2Horizon; omega

end FewExperts.Supplement


