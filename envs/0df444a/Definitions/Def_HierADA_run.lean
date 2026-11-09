-- Prove2me | Definitions.Def_HierADA_run
-- name    : HierADA_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:46.349064+00:00
-- url     : https://prove2.me/theorems/931eb3c4-88ec-4ec9-9ec6-87d416cdd2f8
-- title:
--   Execution of Algorithms 1–2 (with or without correction limits)
-- statement:
--   The execution of the hierarchical mechanism with threshold $\tau$ on the sample blocks $S_1,\dots,S_p$, a noise realization $(E,Z,V)$ and an analyst, for $k$ queries. Initially every score vector is $0$, so all weights are uniform, and the threshold noise $Z_{j,0}$ of every edge is drawn. For each query $f$, chosen by the analyst from the public transcript so far:
--
--   1. **UpdateWeights** (Algorithm 2). Scan the edges $j=1,\dots,p-1$ in order. On edge $j$, the private comparison sets $d=\mu_{j+1}(f)-\mu_j(f)$ and tests $q=+1$, then $q=-1$, each with a fresh test noise $V$, returning the first sign with $q\,d+V\ge\tau+Z_j$, or $0$ if both fail.
--      - If $q=0$, the scan moves to the next edge.
--      - Otherwise a **correction** on edge $j$ is made: $G_j\leftarrow G_j+q\,f(S_j)$; if block $j+1$ is not the anchor, $G_{j+1}\leftarrow G_{j+1}-\frac q4 f(S_{j+1})$; the weights are recomputed by Equation (2); and $T_j\leftarrow T_j+1$. If correction limits $B$ are given and now $T_j=B_j$, the execution stops (the **auxiliary** mechanism). Otherwise the threshold noise of edge $j$ is refreshed and the scan restarts from edge $1$.
--
--      The scan ends when every edge returns $0$.
--   2. **Release** (Algorithm 1, lines 5–6). Set $a=\mu_1(f)+E_t$, clip it to $[0,1]$, round it to the nearest multiple of $\tau/64$, and release it.
--
--   Without limits this is the **original** mechanism. The number of scans per query is capped by a fuel parameter, and the execution is marked finished when all $k$ queries are answered.
--
--   **Formalization Note** (1) Indices are 0-based. (2) The loop bounds are read so that only the edges $1,\dots,p-1$ are scanned and the anchor's score is never updated. As printed, Algorithm 2 scans $j\le p$ and updates $G_{j+1}$ when $j+1\le p$, which would compare a nonexistent block $p+1$ and update the anchor, contrary to p.13 and to the proof of Proposition 3.4 (p.22). (3) Ties in rounding go up. (4) If the fuel runs out, the execution stops unfinished; the auxiliary mechanism is given enough fuel never to run out.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Algorithm 1 (p.13), Algorithm 2, Equation (2) and Compare (p.14), correction limits (Section 3.2, p.18)

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_RunState
import Definitions.Def_HierADA_blockMean
import Definitions.Def_HierADA_Noise

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **An execution of Algorithms 1–2** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data
Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03,
sha256 f220ae51…), Algorithm 1 (p.13), Algorithm 2, Equation (2) and `Compare` (p.14), and the
correction limits of Section 3.2 (p.18).

`run τ n limit fuel S z A k` runs the mechanism with threshold `τ` on the sample blocks `S` (block
`j` has `n j` samples), the noise realization `z = (E, Z, V)` and the analyst `A`, for `k` queries.
Before the first query all scores are `0` and the initial threshold noise `Z_{j,0}` of every edge is
drawn. For query `t` (0-based), the query is `f = A(public transcript so far)`, and then:

* **UpdateWeights (Algorithm 2).** Scan the edges `j = 0, 1, …, p − 2` in order. On edge `j`,
  `Compare` sets `d = μ_{j+1}(f) − μ_j(f)` and tests `q = +1`, then `q = −1`, each with a fresh test
  noise `V`, returning the first sign with `q·d + V ≥ τ + Z_{j,T_j}`, or `0` if both fail. If `q = 0`
  the scan moves to the next edge. Otherwise a **correction** on edge `j`: `G_j ← G_j + q f(S_j)`,
  and, if block `j + 1` is not the anchor, `G_{j+1} ← G_{j+1} − (q/4) f(S_{j+1})`; all weights are
  recomputed by Equation (2) (`blockWeights`); `T_j ← T_j + 1`. If a correction limit `B` is given
  and now `T_j = B_j`, the execution records a halt and stops (the **auxiliary** mechanism);
  otherwise the threshold of edge `j` is refreshed (`Z_{j,T_j}` is drawn) and the scan restarts
  from edge `0`. The scan ends when every edge returns `0`.
* **Release (Algorithm 1, lines 5–6).** Draw `E_t`, set `a = μ_1(f) + E_t`, clip `a` to `[0, 1]`
  and round it to the nearest multiple of `τ/64`; append `(f, a)` to the public transcript.

`finished` is set when all `k` queries were answered.

**Formalization Note.** (1) Indices are 0-based. (2) *Loop bounds* (reading of Algorithm 2): only the
edges `j + 1 < p` exist, the anchor's score is never updated and its weights stay uniform — as printed,
line 2 scans `j ≤ p` and line 6 updates `G_{j+1}` when `j + 1 ≤ p`, which would compare a nonexistent
block `p + 1` and update the anchor, contradicting p.13 and the proof of Proposition 3.4 (p.22).
(3) The threshold noise of edge `j` in its `φ`-th phase is `Z j φ` (phase `φ` starts after `φ`
corrections on that edge), the `m`-th signed test overall uses `V m`, and query `t` uses `E t`.
(4) Rounding uses Lean's `round` (ties go up); the answer is recorded in the augmented transcript by
its grid index. (5) `fuel` bounds the number of scans per query; if it runs out the execution stops
unfinished. The auxiliary mechanism (`limit = some B`) needs at most `∑ B_j + 1` scans per query, and
`auxRun` gives it that much. -/
noncomputable def run {X : Type} (τ : ℝ) {p : ℕ} (n : Fin p → ℕ) (limit : Option (Fin p → ℕ))
    (fuel : ℕ) (S : (j : Fin p) → Fin (n j) → X) (z : Noise) (A : Analyst X) (k : ℕ) :
    RunState X n :=
  queryLoop k 0
    { G := fun _ _ => 0
      T := fun _ => 0
      vIdx := 0
      transcript := []
      queries := []
      aug := []
      corrections := []
      noiseUsed := (List.range (p - 1)).map fun j => z.2.1 j 0
      finished := false }
where
  /-- `Compare(j, f)` on edge `j` (blocks `j` and `j1 = j + 1`). -/
  compare (f : StatisticalQuery X) (st : RunState X n) (j j1 : Fin p) : ℤ × RunState X n :=
    let d := blockMean τ n S st.G j1 f - blockMean τ n S st.G j f
    let th := τ + z.2.1 j.val (st.T j)
    let v1 := z.2.2 st.vIdx
    if th ≤ d + v1 then
      (1, { st with vIdx := st.vIdx + 1, noiseUsed := st.noiseUsed ++ [v1],
                    aug := st.aug ++ [AugEvent.compare j.val 1] })
    else
      let v2 := z.2.2 (st.vIdx + 1)
      if th ≤ -d + v2 then
        (-1, { st with vIdx := st.vIdx + 2, noiseUsed := st.noiseUsed ++ [v1, v2],
                       aug := st.aug ++ [AugEvent.compare j.val (-1)] })
      else
        (0, { st with vIdx := st.vIdx + 2, noiseUsed := st.noiseUsed ++ [v1, v2],
                      aug := st.aug ++ [AugEvent.compare j.val 0] })
  /-- A correction with sign `q` on edge `j`; the Boolean is `true` when a limit is reached. -/
  correct (f : StatisticalQuery X) (st : RunState X n) (j j1 : Fin p) (q : ℤ) :
      Bool × RunState X n :=
    let G1 := Function.update st.G j fun i => st.G j i + (q : ℝ) * (f (S j i) : ℝ)
    let G2 := if j1.val + 1 < p then
        Function.update G1 j1 fun i => G1 j1 i - (q : ℝ) / 4 * (f (S j1 i) : ℝ)
      else G1
    let T' := Function.update st.T j (st.T j + 1)
    let st' := { st with G := G2, T := T', corrections := st.corrections ++ [(j.val, G2)] }
    let refresh := { st' with noiseUsed := st'.noiseUsed ++ [z.2.1 j.val (T' j)] }
    match limit with
    | some B => if T' j = B j then (true, st') else (false, refresh)
    | none => (false, refresh)
  /-- Scan the edges `j, j + 1, …` (at most `rem` of them) until a comparison is nonzero. -/
  pass (f : StatisticalQuery X) : ℕ → ℕ → RunState X n → Option (ℕ × ℤ) × RunState X n
    | 0, _, st => (none, st)
    | rem + 1, j, st =>
      if h : j + 1 < p then
        let r := compare f st ⟨j, by omega⟩ ⟨j + 1, h⟩
        if r.1 = 0 then pass f rem (j + 1) r.2 else (some (j, r.1), r.2)
      else (none, st)
  /-- `UpdateWeights(f)` with at most `fuel` scans: `some false` = done, `some true` = halted,
  `none` = out of fuel. -/
  scan (f : StatisticalQuery X) : ℕ → RunState X n → Option Bool × RunState X n
    | 0, st => (none, st)
    | m + 1, st =>
      match pass f p 0 st with
      | (none, st') => (some false, st')
      | (some (j, q), st') =>
        if h : j + 1 < p then
          let r := correct f st' ⟨j, by omega⟩ ⟨j + 1, h⟩ q
          if r.1 then (some true, r.2) else scan f m r.2
        else (some false, st')
  /-- The query loop of Algorithm 1: `rem` queries left, the next one has index `t`. -/
  queryLoop : ℕ → ℕ → RunState X n → RunState X n
    | 0, _, st => { st with finished := true }
    | rem + 1, t, st =>
      let f := A st.transcript
      let st0 := { st with queries := st.queries ++ [f] }
      match scan f fuel st0 with
      | (some false, st') =>
        let e := z.1 t
        let raw := (if hp : 0 < p then blockMean τ n S st'.G ⟨0, hp⟩ f else 0) + e
        let m : ℤ := round (max 0 (min 1 raw) / (τ / 64))
        queryLoop rem (t + 1)
          { st' with transcript := st'.transcript ++ [(f, (m : ℝ) * (τ / 64))],
                     aug := st'.aug ++ [AugEvent.answer m],
                     noiseUsed := st'.noiseUsed ++ [e] }
      | (some true, st') => { st' with aug := st'.aug ++ [AugEvent.halt] }
      | (none, st') => st'

end HierADA


