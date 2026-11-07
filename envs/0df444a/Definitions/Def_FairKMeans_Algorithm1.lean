-- Prove2me | Definitions.Def_FairKMeans_Algorithm1
-- name    : FairKMeans_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:29.810309+00:00
-- url     : https://prove2.me/theorems/2baa17ef-2931-433e-b305-56636329f332
-- title:
--   Algorithm 1: fair $k$-means by the drift-regularized relaxation, instrumented
-- statement:
--   **Algorithm 1** takes an instance, $\rho\ge1$, $\varepsilon\in(0,1]$, an exact fair-LP oracle, an exact LP (29) oracle and a weighted $k$-means oracle, and runs:
--
--   1. $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, $\lambda=\rho/(1+\rho)$, $T_0=\mathrm{WCS}_\eta(P)$;
--   2. $\phi^*_{T_0}$ from the fair assignment LP of $T_0$, $L_0=\mathrm{Cost}(P,T_0,\phi^*_{T_0})$, $(T,\phi_T)\leftarrow(T_0,\phi^*_{T_0})$;
--   3. repeat: compute $w(t),\pi(t),\nu_p,u_p,P_\lambda$; build $T'=\mathrm{WCS}_{\eta/88}(P_\lambda)$, $V=\mathrm{WCS}_{\eta/4}(U)$ and solve LP (29) for $\phi_{T'}$; compute $g=L(\phi_T)-L(\phi_{T'})$; if $g>\eta L_0/2$, replace $(T,\phi_T)$ by $\big(T\uplus T',(1-\tfrac{\eta}{72})\phi_T\oplus\tfrac{\eta}{72}\phi_{T'}\big)$; until $g\le\eta L_0/2$;
--   4. run the $k$-means oracle on $\pi(T)$ with weights $w(t)$ to get $S_\pi$, and return $S_\pi$ with $\phi^*_{S_\pi}$ from the fair assignment LP of $S_\pi$.
--
--   The loop runs at most $\lceil 576/\eta^2\rceil+1$ iterations, and the result records whether the stopping test ended it. It also records the number of $k$-means calls, the number of linear programs and their sizes, the size of the $k$-means input, the initial pair, $L_0$, the final relaxed solution, and a count of the real-RAM arithmetic operations performed outside the two oracles.
--
--   This is the algorithm whose guarantees Theorem 3 states.
--
--   **Formalization Note** The algorithm is a Lean function of its oracles, hence deterministic. Operation charges (over-charging is harmless): building $\mathrm{WCS}_\delta$ from $q$ points, $q^r r d$; coefficients of the fair LP of $s$ centers, $3nsd$; line 4, $3n|T|d+n|T|+2n|T|d+3nd$; line 5, $3n(|T'|+|V|)d+n|T'||V|$; line 6, $10n(|T|+|T'|)d+10nd$; line 8, $n(|T|+|T'|)$; line 11, $3n|T|d+n|T|$; line 12, $3n|S_\pi|d$. A stopped loop state is a fixed point of the step.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Algorithm 1, p.25 (PDF p.27); footnote 1, p.5 (PDF p.7); operation accounting in the proof of Proposition 29, pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles

namespace FairKMeans

/-!
# Algorithm 1 (fair k-means by the drift-regularized relaxation), instrumented

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Algorithm 1, p.25
(PDF 27), with the cost model of footnote 1, p.5 (PDF 7), and the operation accounting of the
proof of Proposition 29, pp.35–36 (PDF 37–38).

**Formalization Note.** Algorithm 1 is a Lean function of a fair-LP oracle, an LP (29) oracle
and a weighted k-means oracle; it is deterministic because it is a function of its oracles.
Lines 1–13 are transcribed: `η = min{1/10, ε/(3ρ)}`, `λ = ρ/(1+ρ)`, `T₀ = WCS_η(P)`; `φ*_{T₀}`
from the fair-LP oracle and `L₀ = Cost(P, T₀, φ*_{T₀})`; in each iteration `P_λ, U` by (26),
`T' = WCS_{η/88}(P_λ)`, `V = WCS_{η/4}(U)`, `φ_{T'}` from the LP (29) oracle,
`g = L(φ_T) − L(φ_{T'})` with `L` the linearized cost at the current `φ_T`, and the update
`(T ⊎ T', (1 − η/72)φ_T ⊕ (η/72)φ_{T'})` iff `g > ηL₀/2`; then the k-means oracle on `π(T)` with
weights `w(t)`, and the fair-LP oracle on `S_π`.

The `repeat … until` loop runs on a state with a stop flag for at most
`⌈576/η²⌉₊ + 1` iterations (`Nat.iterate`; a stopped state is a fixed point of the step). The
result records whether the stopping test `g ≤ ηL₀/2`, rather than the iteration budget, ended the
loop (`stopped`). Counters: `kmCalls` and `lpCalls` count the oracle calls the code makes (one
k-means call; one LP for `T₀`, one per iteration, one for `S_π`); `lpSizes` lists
(variables, constraints) of every LP solved, in order; `kmInputSize = |T|` at line 11.

**Operation charges** (`arithOps`, real-RAM operations outside the oracles; footnote 1). Every
real operation outside the two oracles is charged at least once (over-charging is harmless):
building `WCS_δ` from `q` points: `q^r·r·d` (`wcsCharge`); coefficients of the fair LP of `s`
centers: `3·n·s·d`; line 4: `3·n·|T|·d + n·|T| + 2·n·|T|·d + 3·n·d`; line 5 coefficients:
`3·n·(|T'|+|V|)·d + n·|T'|·|V|` (plus the two `WCS` builds); line 6: `10·n·(|T|+|T'|)·d + 10·n·d`;
line 8: `n·(|T|+|T'|)`; line 11: `3·n·|T|·d + n·|T|`; line 12: `3·n·|S_π|·d`.
-/

variable {d n m : ℕ}

/-- `η = min{1/10, ε/(3ρ)}` (line 1). -/
noncomputable def eta (ρ ε : ℝ) : ℝ := min (1 / 10) (ε / (3 * ρ))

/-- The iteration budget `⌈576/η²⌉ + 1` of the loop (Lemma 28 and p.36). -/
noncomputable def fuel (ρ ε : ℝ) : ℕ := ⌈576 / eta ρ ε ^ 2⌉₊ + 1

/-- Charge for the coefficients of the fair assignment LP of `s` centers (lines 2 and 12). -/
def fairLPCoeffCharge (n s d : ℕ) : ℕ := 3 * n * s * d

/-- Charge for line 4 (`w(t)`, `π(t)`, `ν_p`, `u_p`, `p_λ`). -/
def line4Charge (n s d : ℕ) : ℕ := 3 * n * s * d + n * s + 2 * n * s * d + 3 * n * d

/-- Charge for the coefficients of LP (29) in line 5. -/
def line5Charge (n s' v d : ℕ) : ℕ := 3 * n * (s' + v) * d + n * s' * v

/-- Charge for line 6 (the gap `g` by (23)). -/
def line6Charge (n s s' d : ℕ) : ℕ := 10 * n * (s + s') * d + 10 * n * d

/-- Charge for line 8 (the mixture). -/
def line8Charge (n s s' : ℕ) : ℕ := n * (s + s')

/-- Charge for line 11 (computing `π(T)` and its weights). -/
def line11Charge (n s d : ℕ) : ℕ := 3 * n * s * d + n * s

/-- The state of the loop of Algorithm 1. -/
structure LoopState (d n : ℕ) where
  /-- `|T|`. -/
  s : ℕ
  /-- The candidate family `T`. -/
  T : Fin s → E d
  /-- The current assignment `φ_T`. -/
  φ : Fin n → Fin s → ℝ
  /-- Whether the stopping test `g ≤ ηL₀/2` has held. -/
  stopped : Bool
  /-- Iterations executed so far. -/
  iterations : ℕ
  /-- Updates (line 8) performed so far. -/
  updates : ℕ
  /-- (variables, constraints) of every LP solved so far. -/
  lpSizes : List (ℕ × ℕ)
  /-- Operations charged so far. -/
  ops : ℕ

/-- One iteration (lines 4–10) of the loop of Algorithm 1; a stopped state is left unchanged. -/
noncomputable def loopStep (ρ ε : ℝ) (I : Instance d n m) (lp29 : LP29Oracle d n) (L₀ : ℝ)
    (st : LoopState d n) : LoopState d n :=
  if st.stopped then st else
    let η := eta ρ ε
    let pl := plam I ρ st.φ
    let u := uvec I ρ st.φ
    let T' := wcs (η / 88) pl
    let V := wcs (η / 4) u
    let φ' := (lp29 (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4)) pl u T' V).1
    let g := linCost I ρ st.φ st.φ - linCost I ρ st.φ φ'
    let ops := st.ops + line4Charge n st.s d + wcsCharge n (η / 88) d + wcsCharge n (η / 4) d
      + line5Charge n (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4)) d
      + line6Charge n st.s (n ^ wcsR (η / 88)) d
    let sizes := st.lpSizes ++ [lp29Size n m (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4))]
    if η * L₀ / 2 < g then
      { s := st.s + n ^ wcsR (η / 88)
        T := mixCand st.T T'
        φ := mixAssign (η / 72) st.φ φ'
        stopped := false
        iterations := st.iterations + 1
        updates := st.updates + 1
        lpSizes := sizes
        ops := ops + line8Charge n st.s (n ^ wcsR (η / 88)) }
    else
      { st with
        stopped := true
        iterations := st.iterations + 1
        lpSizes := sizes
        ops := ops }

/-- The output of Algorithm 1, with its instrumentation. -/
structure Alg1Result (d n : ℕ) where
  /-- `|S_π|`. -/
  s : ℕ
  /-- The returned centers `S_π`. -/
  centers : Fin s → E d
  /-- The returned assignment `φ*_{S_π}`. -/
  assign : Fin n → Fin s → ℝ
  /-- The loop ended by its stopping test (not by the iteration budget). -/
  stopped : Prop
  /-- Number of loop iterations executed. -/
  iterations : ℕ
  /-- Number of updates (line 8) performed. -/
  updates : ℕ
  /-- Number of calls to the k-means oracle. -/
  kmCalls : ℕ
  /-- Number of linear programs solved. -/
  lpCalls : ℕ
  /-- (variables, constraints) of every LP solved, in order. -/
  lpSizes : List (ℕ × ℕ)
  /-- Number of weighted points passed to the k-means oracle. -/
  kmInputSize : ℕ
  /-- Real-RAM operations outside the oracles. -/
  arithOps : ℕ
  /-- `|T₀|`. -/
  initS : ℕ
  /-- `T₀ = WCS_η(P)`. -/
  initT : Fin initS → E d
  /-- `φ*_{T₀}`. -/
  initφ : Fin n → Fin initS → ℝ
  /-- `L₀ = Cost(P, T₀, φ*_{T₀})`. -/
  L₀ : ℝ
  /-- `|T|` at the end of the loop. -/
  relaxedS : ℕ
  /-- The candidate family `T` at the end of the loop. -/
  relaxedT : Fin relaxedS → E d
  /-- The relaxed solution's assignment `φ_T` at the end of the loop. -/
  relaxedφ : Fin n → Fin relaxedS → ℝ

/-- Algorithm 1 (p.25), run with `ρ`, `ε`, an instance and the three oracles. -/
noncomputable def alg1 (ρ ε : ℝ) (I : Instance d n m) (fairLP : FairLPOracle d n)
    (lp29 : LP29Oracle d n) (KM : KMOracle d) : Alg1Result d n :=
  let η := eta ρ ε
  let T₀ := wcs η I.pts
  let φ₀ := fairLP (n ^ wcsR η) T₀
  let L₀ := cost I T₀ φ₀
  let init : LoopState d n :=
    { s := n ^ wcsR η, T := T₀, φ := φ₀, stopped := false, iterations := 0, updates := 0,
      lpSizes := [fairLPSize n m (n ^ wcsR η)],
      ops := wcsCharge n η d + fairLPCoeffCharge n (n ^ wcsR η) d }
  let fin := (loopStep ρ ε I lp29 L₀)^[fuel ρ ε] init
  let out := KM I.k fin.s (cen I fin.φ) (clusterWeight fin.φ)
  { s := out.1
    centers := out.2
    assign := fairLP out.1 out.2
    stopped := fin.stopped = true
    iterations := fin.iterations
    updates := fin.updates
    kmCalls := 1
    lpCalls := fin.iterations + 2
    lpSizes := fin.lpSizes ++ [fairLPSize n m out.1]
    kmInputSize := fin.s
    arithOps := fin.ops + line11Charge n fin.s d + fairLPCoeffCharge n out.1 d
    initS := n ^ wcsR η
    initT := T₀
    initφ := φ₀
    L₀ := L₀
    relaxedS := fin.s
    relaxedT := fin.T
    relaxedφ := fin.φ }

end FairKMeans


