-- Prove2me | Definitions.Def_FairKMeans_Supplement_ConstrainedAlgorithm
-- name    : FairKMeans_Supplement_ConstrainedAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:00:21.55121+00:00
-- url     : https://prove2.me/theorems/e929d0df-bc16-4404-b786-416f809ab735
-- title:
--   The weighted Algorithm 1 for homogeneous cluster constraints, instrumented
-- statement:
--   The **weighted Algorithm 1 with homogeneous cluster constraints** is Algorithm 1 of the paper with "fair" read as "feasible" (proof of Theorem 32) and with every sum over input points weighted by $w(p)$ (Remark 44). With $\eta=\min\{1/10,\varepsilon/(3\rho)\}$ and $\lambda=\rho/(1+\rho)$ it:
--
--   1. sets $T_0=\mathrm{WCS}_\eta(P)$, solves the feasible assignment LP of $T_0$ to get $\phi_{T_0}$, and sets $L_0=\mathrm{Cost}(P,T_0,\phi_{T_0})$;
--   2. repeats: computes $P_\lambda$ and $U$, the candidate sets $T'=\mathrm{WCS}_{\eta/88}(P_\lambda)$ and $V=\mathrm{WCS}_{\eta/4}(U)$, solves LP (29) for $\phi_{T'}$, computes $g=L(\phi_T)-L(\phi_{T'})$, and if $g>\eta L_0/2$ replaces $(T,\phi_T)$ by $(T\uplus T',(1-\eta/72)\phi_T\oplus(\eta/72)\phi_{T'})$, otherwise stops (at most $\lceil576/\eta^2\rceil+1$ iterations);
--   3. calls the weighted $k$-means oracle once, on the centroids $\pi(T)$ with weights $w(t)$, obtaining $S_\pi$;
--   4. returns $S_\pi$ and the optimal solution of the feasible assignment LP of $S_\pi$.
--
--   The result records whether the stopping test ended the loop, the numbers of iterations, $k$-means calls and LPs, the size of every LP, the size of the $k$-means input, and the number of real-RAM operations outside the oracles.
--
--   **Formalization Note** The algorithm is a Lean function of its three oracles, as the published `FairKMeans.alg1`, whose output type, loop state, candidate sets, constants and charges it reuses; the operation charges add the multiplications by $w(p)$.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Algorithm 1, p.25 (PDF p.27); proof of Theorem 32, pp.37–38 (PDF pp.39–40); Remark 44, p.48 (PDF p.50); footnote 1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1
import Definitions.Def_FairKMeans_Supplement_Constrained
import Definitions.Def_FairKMeans_Supplement_ConstrainedLP

namespace FairKMeans.Supplement

/-!
# The weighted Algorithm 1 for homogeneous cluster constraints, instrumented

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Algorithm 1, p.25
(PDF 27), read as in the proof of Theorem 32, pp.37–38 (PDF 39–40: "fair" read as "feasible"),
in the weighted version of Remark 44, p.48 (PDF 50); cost model of footnote 1, p.5 (PDF 7).

**Formalization Note.** This is the published `FairKMeans.alg1` (lines 1–13, the same `η`,
`λ`, candidate sets `WCS_η(P)`, `WCS_{η/88}(P_λ)`, `WCS_{η/4}(U)`, threshold `ηL₀/2`, mixture
weight `η/72`, iteration budget `fuel ρ ε`, output type `Alg1Result` and counters) with two
changes only: (i) both LPs carry the constraints (40) instead of fairness, so their oracles are
specified by `IsHLPOracle` / `IsHLP29Oracle` and their sizes are `hLPSize` / `hlp29Size`;
(ii) weights (Remark 44): `w(t)`, `π(t)`, `C_T`, `C_ν`, `L`, the LP objectives, LP (29)'s
`z`-constraints and `L₀` are the weighted ones; the k-means oracle receives `π(T)` with weights
`w(t)`. **Operation charges** are the published ones plus the multiplications by `w(p)`:
`n·s` for the coefficients of an assignment LP of `s` centers, `n·|T|` in line 4,
`n·|T'|·|V|` in line 5, `n·(|T|+|T'|) + n` in line 6 and `n·|T|` in line 11
(over-charging is harmless).
-/

open FairKMeans

variable {d n r : ℕ}

/-- Charge for the coefficients `w(p)‖p − s‖²` of the assignment LP of `s` centers. -/
def hLPCoeffCharge (n s d : ℕ) : ℕ := fairLPCoeffCharge n s d + n * s

/-- Charge for line 4 (weighted `w(t)`, `π(t)`; `ν_p`, `u_p`, `p_λ`). -/
def hline4Charge (n s d : ℕ) : ℕ := line4Charge n s d + n * s

/-- Charge for the coefficients of the weighted LP (29) in line 5. -/
def hline5Charge (n s' v d : ℕ) : ℕ := line5Charge n s' v d + n * s' * v

/-- Charge for line 6 (the weighted gap `g`). -/
def hline6Charge (n s s' d : ℕ) : ℕ := line6Charge n s s' d + n * (s + s') + n

/-- Charge for line 11 (computing `π(T)` and the weights `w(t)`). -/
def hline11Charge (n s d : ℕ) : ℕ := line11Charge n s d + n * s

/-- One iteration (lines 4–10) of the weighted, constrained loop; a stopped state is left
unchanged. -/
noncomputable def hloopStep (ρ ε : ℝ) (I : HInstance d n r) (lp29 : LP29Oracle d n) (L₀ : ℝ)
    (st : LoopState d n) : LoopState d n :=
  if st.stopped then st else
    let η := eta ρ ε
    let pl := hplam I ρ st.φ
    let u := huvec I ρ st.φ
    let T' := wcs (η / 88) pl
    let V := wcs (η / 4) u
    let φ' := (lp29 (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4)) pl u T' V).1
    let g := hlinCost I ρ st.φ st.φ - hlinCost I ρ st.φ φ'
    let ops := st.ops + hline4Charge n st.s d + wcsCharge n (η / 88) d + wcsCharge n (η / 4) d
      + hline5Charge n (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4)) d
      + hline6Charge n st.s (n ^ wcsR (η / 88)) d
    let sizes := st.lpSizes ++ [hlp29Size n r (n ^ wcsR (η / 88)) (n ^ wcsR (η / 4))]
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

/-- The weighted Algorithm 1 for homogeneous cluster constraints (p.25 with p.37 and Remark 44),
run with `ρ`, `ε`, an instance and the three oracles. -/
noncomputable def alg1H (ρ ε : ℝ) (I : HInstance d n r) (hLP : FairLPOracle d n)
    (lp29 : LP29Oracle d n) (KM : KMOracle d) : Alg1Result d n :=
  let η := eta ρ ε
  let T₀ := wcs η I.pts
  let φ₀ := hLP (n ^ wcsR η) T₀
  let L₀ := hcost I T₀ φ₀
  let init : LoopState d n :=
    { s := n ^ wcsR η, T := T₀, φ := φ₀, stopped := false, iterations := 0, updates := 0,
      lpSizes := [hLPSize n r (n ^ wcsR η)],
      ops := wcsCharge n η d + hLPCoeffCharge n (n ^ wcsR η) d }
  let fin := (hloopStep ρ ε I lp29 L₀)^[fuel ρ ε] init
  let out := KM I.k fin.s (hcen I fin.φ) (hclusterWeight I fin.φ)
  { s := out.1
    centers := out.2
    assign := hLP out.1 out.2
    stopped := fin.stopped = true
    iterations := fin.iterations
    updates := fin.updates
    kmCalls := 1
    lpCalls := fin.iterations + 2
    lpSizes := fin.lpSizes ++ [hLPSize n r out.1]
    kmInputSize := fin.s
    arithOps := fin.ops + hline11Charge n fin.s d + hLPCoeffCharge n out.1 d
    initS := n ^ wcsR η
    initT := T₀
    initφ := φ₀
    L₀ := L₀
    relaxedS := fin.s
    relaxedT := fin.T
    relaxedφ := fin.φ }

end FairKMeans.Supplement


