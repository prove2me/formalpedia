-- Prove2me | Definitions.Def_OnlineShadow_LogRate_alg1Run
-- name    : OnlineShadow_LogRate_alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:11:11.944835+00:00
-- url     : https://prove2.me/theorems/c2f01bda-2261-4f8f-b102-260eef4a08bd
-- title:
--   Run of Algorithm 1 (ONLINESHADOWTOMOGRAPHY1) on an outcome string
-- statement:
--   Algorithm 1 has parameters: the number of rounds $m$, the accuracy $\varepsilon$, an integer mistake budget $K$ and the logistic sharpness $\lambda$, on $n$ copies. It starts with $H=0$, $n_{\mathsf{mstk}}=0$, failed $=$ false. In each round $t$ it receives $A^{(t)}$ from the adversary as a function of the transcript. If it has failed it outputs $1/2$. Otherwise it repeats the following pass:
--
--   1. $\rho_H\leftarrow e^{-H}/\mathrm{Tr}(e^{-H})$, $\nu\leftarrow\mathrm{Tr}(A^{(t)}\rho_H)$, $L\leftarrow\bot$;
--   2. if $\nu\le1-3\varepsilon/4$, perform the soft binary measurement of $(A^{(t)},\nu+3\varepsilon/4)$; on a flag set $L\leftarrow-A^{(t)}$;
--   3. if $L=\bot$ and $\nu\ge3\varepsilon/4$, perform the soft binary measurement of $(1-A^{(t)},1-\nu+3\varepsilon/4)$; on a flag set $L\leftarrow A^{(t)}$;
--   4. if $L\ne\bot$: $H\leftarrow H+\frac\varepsilon8L$, $n_{\mathsf{mstk}}\leftarrow n_{\mathsf{mstk}}+1$, and failed $\leftarrow$ true if $n_{\mathsf{mstk}}=K$;
--
--   until $L=\bot$ or failed. It then outputs $1/2$ if it has failed and $\nu$ otherwise.
--
--   A run is determined by the outcomes of its measurements. Reading them in order from a string $\omega\in\{\text{flag},\text{pass}\}^{2(m+K)}$, this definition records the run: the measurements performed with their outcomes, the product of their Kraus operators (latest on the left), the observables and the outputs. Companion definitions extract the Kraus operator of $\omega$ (`alg1Kraus`), the output of round $t$ (`alg1Out`) and the observable of round $t$ (`alg1Obs`).
--
--
--   **Formalization Note** A run performs at most $2(m+K)$ soft binary measurements (p. 12). The Kraus operator of $\omega$ multiplies in, for every coordinate the run does not use, $1$ if it is pass and $0$ if it is flag (a trivial measurement), so the probabilities of all strings sum to $1$. The repeat loop is given $K+1$ passes, which it never exhausts when $K\ge1$. Rounds are numbered from $0$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Algorithm 1, p. 11; §4.2, p. 12

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_Adversary
import Definitions.Def_OnlineShadow_LogRate_softKraus
import Definitions.Def_OnlineShadow_LogRate_gibbs

namespace OnlineShadow.LogRate

/-- One soft binary measurement performed by Algorithm 1: the measured single-copy observable `obs`
(`A⁽ᵗ⁾` or `1 − A⁽ᵗ⁾`), its threshold `thr`, and the outcome (`true` = flag, `false` = pass). -/
structure Alg1Step (d : ℕ) where
  obs : Matrix (Fin d) (Fin d) ℂ
  thr : ℝ
  flag : Bool

/-- The state of a run of Algorithm 1: the MMW matrix `H`, the mistake counter `nmstk`, the flag
`failed`, the pointer `ptr` to the next unused outcome coordinate, the product `kraus` of the Kraus
operators applied so far (latest on the left), the list `steps` of measurements performed, and the
transcript of (observable, output) pairs. -/
structure Alg1State (d n : ℕ) where
  H : Matrix (Fin d) (Fin d) ℂ
  nmstk : ℕ
  failed : Bool
  ptr : ℕ
  kraus : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ
  steps : List (Alg1Step d)
  transcript : List (Matrix (Fin d) (Fin d) ℂ × ℝ)

/-- Coordinate `s` of an outcome string, read as `false` past its end. -/
def alg1Bit {N : ℕ} (ω : Fin N → Bool) (s : ℕ) : Bool :=
  if h : s < N then ω ⟨s, h⟩ else false

/-- Perform the soft binary measurement corresponding to `(B, θ)` with the outcome `ω ptr`: record the
step, multiply its Kraus operator onto the product, advance the pointer. Returns the outcome. -/
noncomputable def alg1Measure {d : ℕ} (n : ℕ) (ε lam : ℝ) {N : ℕ} (ω : Fin N → Bool)
    (B : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) (st : Alg1State d n) : Alg1State d n × Bool :=
  let b := alg1Bit ω st.ptr
  ({ st with
      ptr := st.ptr + 1
      kraus := softKraus n ε lam θ B b * st.kraus
      steps := st.steps ++ [⟨B, θ, b⟩] }, b)

/-- One pass of the repeat loop of Algorithm 1 (lines 8–18, p.11) on the observable `A`. Returns the new
state, whether no test flagged (`L = ⊥`), and the value `ν = Tr(A ρ_H)`. -/
noncomputable def alg1Pass {d : ℕ} (n K : ℕ) (ε lam : ℝ) {N : ℕ} (ω : Fin N → Bool)
    (A : Matrix (Fin d) (Fin d) ℂ) (st : Alg1State d n) : Alg1State d n × Bool × ℝ :=
  let ν := (A * gibbs st.H).trace.re
  -- line 10–12: high test on `A`, skipped when `ν > 1 − 3ε/4`; a flag sets `L ← −A`
  let r1 : Alg1State d n × Option (Matrix (Fin d) (Fin d) ℂ) :=
    if ν ≤ 1 - 3 * ε / 4 then
      let p := alg1Measure n ε lam ω A (ν + 3 * ε / 4) st
      (p.1, if p.2 then some (-A) else none)
    else (st, none)
  -- lines 13–15: high test on `1 − A`, skipped when `ν < 3ε/4` or the first test flagged; a flag sets `L ← A`
  let r2 : Alg1State d n × Option (Matrix (Fin d) (Fin d) ℂ) :=
    if r1.2.isNone ∧ 3 * ε / 4 ≤ ν then
      let p := alg1Measure n ε lam ω (1 - A) (1 - ν + 3 * ε / 4) r1.1
      (p.1, if p.2 then some A else none)
    else r1
  -- lines 16–18: on a flag, `H ← H + (ε/8) L`, count the mistake, fail when the budget is reached
  match r2.2 with
  | none => (r2.1, true, ν)
  | some L =>
    ({ r2.1 with
        H := r2.1.H + (((ε / 8 : ℝ)) : ℂ) • L
        nmstk := r2.1.nmstk + 1
        failed := r2.1.failed || decide (r2.1.nmstk + 1 = K) }, false, ν)

/-- The repeat loop of Algorithm 1 (lines 7–19), with `fuel` passes at most: it stops when no test
flagged or the run has failed. Returns the final state and the last `ν`. -/
noncomputable def alg1Loop {d : ℕ} (n K : ℕ) (ε lam : ℝ) {N : ℕ} (ω : Fin N → Bool)
    (A : Matrix (Fin d) (Fin d) ℂ) : ℕ → Alg1State d n → Alg1State d n × ℝ
  | 0, st => (st, 1 / 2)
  | fuel + 1, st =>
    let r := alg1Pass n K ε lam ω A st
    if r.2.1 || r.1.failed then (r.1, r.2.2) else alg1Loop n K ε lam ω A fuel r.1

/-- One round of Algorithm 1 (lines 3–23): receive `A` from the adversary on the transcript, answer `1/2`
if the run has failed, otherwise run the repeat loop (at most `K + 1` passes) and answer `ν`, or `1/2` if
the budget was exhausted in this round. -/
noncomputable def alg1Round {d : ℕ} (n K : ℕ) (ε lam : ℝ) (adv : Adversary d) {N : ℕ}
    (ω : Fin N → Bool) (st : Alg1State d n) : Alg1State d n :=
  let A := adv.obs st.transcript
  if st.failed then { st with transcript := st.transcript ++ [(A, 1 / 2)] }
  else
    let r := alg1Loop n K ε lam ω A (K + 1) st
    { r.1 with transcript := r.1.transcript ++ [(A, if r.1.failed then 1 / 2 else r.2)] }

/-- The run of **Algorithm 1** (ONLINESHADOWTOMOGRAPHY1, Chen, O'Donnell, Pelecanos, Wright, *Online
Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026,
sha256 90993723…dc3a9), p.11) for `m` rounds, mistake budget `K`, accuracy `ε` and logistic sharpness
`λ` on `n` copies, against the adversary `adv`, with the measurement outcomes read in order from the
outcome string `ω : Fin (2(m + K)) → Bool` (`true` = flag). Starts from `H = 0`, `nmstk = 0`,
`failed = false`.

**Formalization Note** (paper.md R11) The run is deterministic given `ω`; a run performs at most
`2(m + K)` soft binary measurements (p.12), and coordinates past the end of `ω` would read as `false`.
The repeat loop is given `K + 1` passes, which it never exhausts when `K ≥ 1`: every pass but the last
of a round increments `nmstk`, and the run fails when `nmstk = K`. -/
noncomputable def alg1Run {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d)
    (ω : Fin (2 * (m + K)) → Bool) : Alg1State d n :=
  (List.range m).foldl (fun st _ => alg1Round n K ε lam adv ω st)
    ⟨0, 0, false, 0, 1, [], []⟩

/-- The Kraus operator of the outcome string `ω` in Algorithm 1: the product, in time order (latest on
the left), of the Kraus operators of the measurements performed, times `∏` over the unused coordinates
`s` of `1` if `ω s = false` and `0` if `ω s = true` (the trivial measurement with Kraus pair `(0, 1)`
for (flag, pass)), so that the probabilities of all outcome strings sum to `1` (paper.md R11). -/
noncomputable def alg1Kraus {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d)
    (ω : Fin (2 * (m + K)) → Bool) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  (∏ s : Fin (2 * (m + K)),
      if (alg1Run n m K ε lam adv ω).ptr ≤ s.val ∧ ω s = true then (0 : ℂ) else 1) •
    (alg1Run n m K ε lam adv ω).kraus

/-- The output `μ̂⁽ᵗ⁾` of round `t` (rounds numbered from `0`) of Algorithm 1 on the outcome string
`ω` (`0` for `t ≥ m`, never used). -/
noncomputable def alg1Out {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d)
    (ω : Fin (2 * (m + K)) → Bool) (t : ℕ) : ℝ :=
  ((alg1Run n m K ε lam adv ω).transcript.getD t (0, 0)).2

/-- The observable `A⁽ᵗ⁾` the adversary queried in round `t` (from `0`) of Algorithm 1 on the outcome
string `ω`. -/
noncomputable def alg1Obs {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (adv : Adversary d)
    (ω : Fin (2 * (m + K)) → Bool) (t : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  ((alg1Run n m K ε lam adv ω).transcript.getD t (0, 0)).1

end OnlineShadow.LogRate


