-- Prove2me | Definitions.Def_PPRInstOpt_UnknownN_TriPPR
-- name    : PPRInstOpt_UnknownN_TriPPR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:13:26.305202+00:00
-- url     : https://prove2.me/theorems/a2ef9bcf-0f72-44b2-86c2-1bce141fb9ab
-- title:
--   TriPPR (Algorithms 8 and 9) on the randomized RAM: rounds, estimates X_γ^(i), τ^(i), i^R, i*, output and running time
-- statement:
--   The random tape $\omega$ has i.i.d. uniform $[0,1]$ entries (`tapeLaw`, an infinite product measure) and is read as a countable family of independent streams. A **discounted walk** from $u$ reads entries in order: it stops at the current vertex if the entry is $<\alpha$, else moves to out-neighbour number $\min\{\lfloor d\,x\rfloor,d-1\}$ of the current vertex ($d$ its out-degree, $x$ the next entry); each step costs five units.
--
--   **MonteCarloR$(q)$** (Algorithm 9) with forward results $(r_f,p_f,F_f,R_f)$ and backward results $(r_b,p_b,F_b,\bar r_b)$ returns
--   $$X=p_b(s)+\sum_{v\notin F_b}p_f(v)r_b(v)+\sum_{u\notin F_f,\ r_f(u)>0}\ \sum_{k=1}^{q(u)}\frac{r_f(u)\,r_b(v_k(u))}{q(u)}\,\mathbf 1[v_k(u)\notin F_b],$$
--   with $q(u)=\lceil q\,r_f(u)/R_f\rceil$ walks from $u$ ending at $v_k(u)$, or just the first two terms if $R_f\bar r_b=0$.
--
--   **TriPPR$(s,t,\varepsilon_r)$** (Algorithm 8): in round $i=1,2,\dots$ run Algorithm 6 from $s$ and Algorithm 7 from $t$ with budget $2^i$, keep the forward results with the smallest $R_f$ and the backward results with the smallest $\bar r_b$ seen so far ($R'_f=\bar r'_b=1$ initially, `≤` replaces), compute $X_\gamma^{(i)}$ = MonteCarloR$(2^i)$ with the kept results on stream $(i,\gamma)$ for $\gamma=1,2,3$, and stop with output $X_3^{(i)}$ at the first round with
--   $$\max\{X_1^{(i)},X_2^{(i)}\}\ \ge\ \tau^{(i)}=\frac{1024\,R_f^{(i)}\,\bar r_b^{(i)}}{\varepsilon_r^2\,2^i}.$$
--   `stopRound` is $i^R$, `triOutput` is $X_3^{(i^R)}$, `triHalts` says some round stops and every walk of rounds $1,\dots,i^R$ ends. `triTime` is $1+\sum_{i\le i^R}$ (time of Algorithms 6 and 7 with budget $2^i$ + time of the three MonteCarloR calls + 4) if it halts, $\top$ otherwise. `istar` is $i^*$, the least $i\ge 1$ with $\tau^{(i)}\le 32\pi(s,t)$.
--
--   **Formalization Note** The program is generic in the vertex type with decidable equality only: it never sees $n$, $m$ or $V$ and reaches only $s$, $t$ and vertices returned by the oracle. Round quantities exist for every round (the all-rounds variant of p. 27) because each call has its own stream.
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 24, 26-27, §4.1–4.2, Algorithms 8 and 9, Eqs. (19)–(20)

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_Freezing

/-!
# TriPPR (Algorithms 8 and 9) on the randomized RAM with the adjacency-list oracle

The machine: a unit-cost RAM with exact real arithmetic, memory addressed by integers and by
(opaque) vertex labels, the four oracle queries of `Oracle`, and unit-cost random draws. The
random tape is `ω : ℕ → [0, 1]` with independent uniform entries (`tapeLaw`); it is read as a
countable family of independent streams, stream `j` being `k ↦ ω (Nat.pair j k)`. A Bernoulli(α)
draw from entry `x` is `x < α`; a uniform index in `{0, …, d-1}` is `min ⌊d x⌋ (d-1)`.
Each `MonteCarloR_γ` call of round `i` of Algorithm 8 reads its own stream `Nat.pair i γ`, which
makes the three calls of a round and the rounds independent, as Algorithm 8 requires.

The program is generic in the vertex type with only decidable equality: it never knows `n`, `m`
or `V`, and can only reach `s`, `t` and vertices returned by the oracle.

A step of a discounted walk costs five units (a Bernoulli(α) draw, an `outdeg` query, a uniform
index draw, an `out` query, a branch); every other line costs one unit per elementary operation as
charged below. The time of a run is the sum over the rounds executed; a run that never stops has
time `⊤`.
-/

open MeasureTheory

namespace PPRInstOpt.UnknownN

/-- The random tape: independent uniform draws from `[0, 1]`. -/
abbrev Tape := ℕ → unitInterval

/-- The law of the random tape: the product of uniform laws on `[0, 1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- Stream `j` of the tape. -/
def stream (ω : Tape) (j : ℕ) : Tape := fun k => ω (Nat.pair j k)

variable {V : Type} [DecidableEq V]

/-- An `α`-discounted random walk from `u`, reading tape entries `pos, pos+1, …`: at each step stop
with probability `α` (entry `< α`), otherwise move to out-neighbour number `min ⌊d x⌋ (d-1)` of the
current vertex, `d` its out-degree, `x` the next entry. With at most `fuel` steps it returns the
endpoint, the next unread position and the number of steps; `none` if the fuel runs out. -/
noncomputable def walk (o : Oracle V) (α : ℝ) (ω : Tape) : ℕ → V → ℕ → Option (V × ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, u, pos =>
    if ((ω pos : unitInterval) : ℝ) < α then some (u, pos + 1, 1)
    else
      let d := o.outdeg u
      let i := min ⌊(d : ℝ) * ((ω (pos + 1) : unitInterval) : ℝ)⌋₊ (d - 1)
      match o.outNbr u i with
      | none => none
      | some w => (walk o α ω fuel w (pos + 2)).map (fun x => (x.1, x.2.1, x.2.2 + 1))

/-- `MonteCarloR(q)` (Algorithm 9, p. 26) with forward results `F` (fields `r, p, frozen, R` =
`r_f, p_f, F_f, R_f`) and backward results `B` (`r_b, p_b, F_b, \bar r_b`), reading the tape `ω`,
with at most `fuel` steps per walk: `X ← p_b(s) + Σ_{v ∉ F_b} p_f(v) r_b(v)`; if
`R_f \bar r_b = 0` return `X`; for each `u ∉ F_f` with `r_f(u) > 0`, `q(u) ← ⌈q r_f(u)/R_f⌉` walks
from `u`, each adding `r_f(u) r_b(v)/q(u)` if its endpoint `v ∉ F_b`. Returns `X` and the RAM time,
or `none` if some walk runs out of fuel. (`p_f` vanishes off the vertices forward push reached, so
the sum over `v ∉ F_b` is a sum over those.) -/
noncomputable def mcRun (o : Oracle V) (α : ℝ) (s : V) (q : ℕ) (F B : PushState V) (ω : Tape)
    (fuel : ℕ) : Option (ℝ × ℕ) :=
  let X0 := B.p s + ((F.seen.filter (fun v => !B.frozen v)).map (fun v => F.p v * B.r v)).sum
  let c0 := 2 + F.seen.length
  if F.R * B.R = 0 then some (X0, c0) else
  let us := F.seen.filter (fun u => !F.frozen u && decide (0 < F.r u))
  let res := us.foldl
    (fun acc u =>
      let qu := ⌈(q : ℝ) * F.r u / F.R⌉₊
      (List.range qu).foldl
        (fun acc' _ => acc'.bind fun st =>
          (walk o α ω fuel u st.2.1).map fun w =>
            (if B.frozen w.1 then st.1 else st.1 + F.r u * B.r w.1 / (qu : ℝ),
              w.2.1, st.2.2 + 2 + 5 * w.2.2))
        (acc.map fun st => (st.1, st.2.1, st.2.2 + 2)))
    (some (X0, 0, c0 + us.length))
  res.map fun st => (st.1, st.2.2)

/-- The `MonteCarloR` call terminates (every walk stops). -/
def mcHalts (o : Oracle V) (α : ℝ) (s : V) (q : ℕ) (F B : PushState V) (ω : Tape) : Prop :=
  ∃ fuel, (mcRun o α s q F B ω fuel).isSome

/-- The least sufficient fuel (the run is the same for every larger fuel). -/
noncomputable def mcFuel (o : Oracle V) (α : ℝ) (s : V) (q : ℕ) (F B : PushState V) (ω : Tape) :
    ℕ :=
  sInf {fuel | (mcRun o α s q F B ω fuel).isSome}

/-- The estimate `X` returned by `MonteCarloR` (`0` on the null event that a walk never stops). -/
noncomputable def mcValue (o : Oracle V) (α : ℝ) (s : V) (q : ℕ) (F B : PushState V) (ω : Tape) :
    ℝ :=
  ((mcRun o α s q F B ω (mcFuel o α s q F B ω)).map Prod.fst).getD 0

/-- The RAM time of the `MonteCarloR` call. -/
noncomputable def mcCost (o : Oracle V) (α : ℝ) (s : V) (q : ℕ) (F B : PushState V) (ω : Tape) :
    ℕ :=
  ((mcRun o α s q F B ω (mcFuel o α s q F B ω)).map Prod.snd).getD 0

/-- The forward results kept after round `i` of Algorithm 8 (lines 1, 3, 5): round `i` runs
`ForwardPushWithFreezing(s, 2^i)` and replaces the kept results when its `R_f ≤ R'_f`; before round
`1`, `R'_f = 1`. Field `R` of `keptFwd i` is `R_f^(i)` (Eq. (20)). -/
noncomputable def keptFwd (o : Oracle V) (α εr : ℝ) (s : V) : ℕ → PushState V
  | 0 => pushInit s 1
  | i + 1 =>
    let F := fwdFinal o α εr (2 ^ (i + 1)) s
    if F.R ≤ (keptFwd o α εr s i).R then F else keptFwd o α εr s i

/-- The backward results kept after round `i` (lines 1, 4, 6); field `R` is `\bar r_b^(i)`. -/
noncomputable def keptBwd (o : Oracle V) (α εr : ℝ) (t : V) : ℕ → PushState V
  | 0 => pushInit t 1
  | i + 1 =>
    let B := bwdFinal o α εr (2 ^ (i + 1)) t
    if B.R ≤ (keptBwd o α εr t i).R then B else keptBwd o α εr t i

/-- `τ^(i) = 1024 R_f^(i) \bar r_b^(i) / (εr² 2^i)` (line 9 of Algorithm 8; Eq. (20)). -/
noncomputable def tau (o : Oracle V) (α εr : ℝ) (s t : V) (i : ℕ) : ℝ :=
  1024 * (keptFwd o α εr s i).R * (keptBwd o α εr t i).R / (εr ^ 2 * 2 ^ i)

/-- `X_γ^(i)`: the estimate of the `γ`-th `MonteCarloR(2^i)` call of round `i` (line 8), on stream
`Nat.pair i γ` of the tape. Defined for every round (the all-rounds variant of p. 27). -/
noncomputable def roundX (o : Oracle V) (α εr : ℝ) (s t : V) (γ i : ℕ) (ω : Tape) : ℝ :=
  mcValue o α s (2 ^ i) (keptFwd o α εr s i) (keptBwd o α εr t i) (stream ω (Nat.pair i γ))

/-- The `γ`-th `MonteCarloR` call of round `i` terminates. -/
def roundHalts (o : Oracle V) (α εr : ℝ) (s t : V) (γ i : ℕ) (ω : Tape) : Prop :=
  mcHalts o α s (2 ^ i) (keptFwd o α εr s i) (keptBwd o α εr t i) (stream ω (Nat.pair i γ))

/-- The stopping criterion (19) in round `i`: `max{X_1^(i), X_2^(i)} ≥ τ^(i)` (line 10). -/
def stopsAt (o : Oracle V) (α εr : ℝ) (s t : V) (i : ℕ) (ω : Tape) : Prop :=
  tau o α εr s t i ≤ max (roundX o α εr s t 1 i ω) (roundX o α εr s t 2 i ω)

/-- `i^R`: the first round `i ≥ 1` whose stopping criterion holds. -/
noncomputable def stopRound (o : Oracle V) (α εr : ℝ) (s t : V) (ω : Tape) : ℕ :=
  sInf {i | 1 ≤ i ∧ stopsAt o α εr s t i ω}

/-- TriPPR halts on tape `ω`: some round stops, and every `MonteCarloR` call of rounds
`1, …, i^R` terminates. -/
def triHalts (o : Oracle V) (α εr : ℝ) (s t : V) (ω : Tape) : Prop :=
  (∃ i, 1 ≤ i ∧ stopsAt o α εr s t i ω) ∧
    ∀ j, 1 ≤ j → j ≤ stopRound o α εr s t ω → ∀ γ ∈ ({1, 2, 3} : Finset ℕ),
      roundHalts o α εr s t γ j ω

/-- The output `\hat π(s, t) = X_3^(i^R)` of `TriPPR(s, t, εr)` (Algorithm 8, line 10). -/
noncomputable def triOutput (o : Oracle V) (α εr : ℝ) (s t : V) (ω : Tape) : ℝ :=
  roundX o α εr s t 3 (stopRound o α εr s t ω) ω

/-- The RAM time of round `i`: Algorithm 6 and Algorithm 7 with budget `2^i`, the three
`MonteCarloR(2^i)` calls, and four units for lines 5, 6, 9, 10. -/
noncomputable def roundCost (o : Oracle V) (α εr : ℝ) (s t : V) (i : ℕ) (ω : Tape) : ℕ :=
  (fwdFinal o α εr (2 ^ i) s).cost + (bwdFinal o α εr (2 ^ i) t).cost + 4 +
    ∑ γ ∈ ({1, 2, 3} : Finset ℕ),
      mcCost o α s (2 ^ i) (keptFwd o α εr s i) (keptBwd o α εr t i) (stream ω (Nat.pair i γ))

open scoped Classical in
/-- The running time of `TriPPR(s, t, εr)` on tape `ω`: one unit for line 1 plus the time of
rounds `1, …, i^R` if it halts, `⊤` otherwise. -/
noncomputable def triTime (o : Oracle V) (α εr : ℝ) (s t : V) (ω : Tape) : ℕ∞ :=
  if triHalts o α εr s t ω then
    ((1 + ∑ i ∈ Finset.Icc 1 (stopRound o α εr s t ω), roundCost o α εr s t i ω : ℕ) : ℕ∞)
  else ⊤

section Fintype

variable [Fintype V]

/-- `i*` (Eq. (20), p. 27): the smallest round `i ≥ 1` with `τ^(i) ≤ 32 π(s, t)` (the set is
nonempty when `π(s, t) > 0`, since `τ^(i) ≤ 1024/(εr² 2^i)`). -/
noncomputable def istar (α εr : ℝ) (G : Digraph V) (s t : V) : ℕ :=
  sInf {i | 1 ≤ i ∧ tau G.oracle α εr s t i ≤ 32 * ppr α G s t}

end Fintype

end PPRInstOpt.UnknownN


