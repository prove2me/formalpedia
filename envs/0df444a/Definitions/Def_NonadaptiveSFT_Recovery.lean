-- Prove2me | Definitions.Def_NonadaptiveSFT_Recovery
-- name    : NonadaptiveSFT_Recovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:46.525656+00:00
-- url     : https://prove2.me/theorems/ea15cf57-79c9-4e78-86d2-f64ffb2205ee
-- title:
--   The recovery algorithm of §6.1 (support-identification loop), the final estimator of §6.3, and the query count $Q_{total}$ of (50)
-- statement:
--   Constants (36): $\delta_{loc}=\delta_{est}=1/30$, $\bar\sigma=\sqrt s\,\tau$, $T_{min}=\tau/2$, $K=31000s$, $\gamma=\delta_{loc}/K$.
--
--   **Support identification** (steps 1–4 of §6.1). Step 1: $S=\emptyset$, $C_S=0$, $\kappa_{tot}=0$; if $M_\emptyset=0$ return $0$, else $T=M_\emptyset$. Each round: compute $\kappa=M_S^2/T^2$ and abort if $\kappa<1$, $T<T_{min}$ or $\kappa_{tot}+\kappa>K$; otherwise the call is made and $\kappa_{tot}$ increases by $\kappa$. The locator call returns a set $S_{new}$ or aborts (then abort); abort if $|S\cup S_{new}|\ge17s$, else $S\leftarrow S\cup S_{new}$. The least-squares routine aborts if $A_S^*A_S$ is singular, else updates $C_S$, $M_S$. If $M_S=0$ return $C_S$; if $T=T_{min}$ leave the loop for the final estimation with support $S$; else
--
--   $$T\leftarrow\max\{T_{min},\min\{T/2,M_S\}\}$$
--
--   and start the next round. Call $i$ succeeds if it returns a list containing every $f$ with $|(\widehat X-C_{S_i})(f)|\ge T_i$ and only frequencies with $|(\widehat X-C_{S_i})(f)|>T_i/2$.
--
--   **Final estimation** (§6.3). With $v_c=\lceil16384b_{ls}^2s\rceil$, $r_c=2\lceil\log(17s/\delta_{est})\rceil+1$ and uniform points $t_{i,j}$, the residual $R(t)=X(t)-\sum_{f\in S}C_S(f)\chi_f(t)$ gives group means $\mu_i(f)=\frac1{v_c}\sum_jR(t_{i,j})\overline{\chi_f(t_{i,j})}$, and $\widetilde X(f)=\lambda(f)+C_S(f)$ on $S$ (with $\lambda(f)$ the coordinatewise median of the $\mu_i(f)$) and $0$ off $S$.
--
--   **Query count** (50): $Q_{total}=n_{ls}+Q_{node}+2048Kq^*+r_cv_c$ with $Q_{node}=15C_0(\log N)\sum_{w\in W_{K'}}w\lceil2A_0K/w\rceil$, $K'=2^{\lceil\log K\rceil}$, $q^*=8\lceil\log(3D/\gamma)\rceil+1$, $D=\frac{42K\log N}{\theta\gamma}\varphi_{max}$, $\varphi_{max}=(3K\log N/\gamma)^{1/4}$, $A_0=128$, $C_0=2^{30}$, $\theta=2^{-28}$.
--
--   **Formalization Note** The loop is a deterministic function of the signal, the least-squares sample, $s$, $\tau$ and an arbitrary sequence of locator outcomes (none = the call aborts), so statements about it hold for every locator. Round $i$ is the $i$-th pass through step 2; $S_i$, $T_i$, $\kappa_i$ are read from the state reached after round $i-1$. Algorithm 1 on p.15 also aborts when $T\le0$; this never happens on a reachable state, and the loop follows §6.1.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), constants (36), p.33; §6.1, p.34; §6.2, pp.34–35; §6.3 and (43), p.37; §7.1, (49), (50), p.40 (PDF pp.35–42)

import Mathlib
import Definitions.Def_NonadaptiveSFT_LeastSquares

open scoped BigOperators

namespace NonadaptiveSFT

/-!
# The recovery algorithm of §6.1, its support-identification loop, the final coefficient estimator
of §6.3, and the query allocation (50) of §7.1

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…), constants (36), p.33; §6.1 steps 1–5, p.34; the round
and call terminology of §6.2, pp.34–35; §6.3, (43) and the estimator, p.37; §7.1, (49), (50), p.40
(PDF pp.35–42).

Constants (36): "δ_loc = δ_est = 1/30, σ̄ = √s τ, T_min = τ/2, K = 31000s, γ = δ_loc/K".

**Formalization Note.**
* The support-identification loop (steps 1–4 of §6.1) is a deterministic function of the signal
  `X`, the least-squares sample `U`, the parameters `s`, `τ`, and an **arbitrary** sequence of
  locator outcomes `loc : ℕ → Option (Finset G)`: `loc i = none` means locator call `i` aborts,
  `loc i = some L` that it returns `L`. Lemma 16 and Corollary 17 are stated for every such
  sequence, i.e. for every locator.
* `loopAt … 0` is the state after step 1; `loopAt … i` is the state after round `i` (the `i`-th
  pass through step 2, which makes call `i`). Round `i` is reached when `loopAt … (i−1)` is
  `running S_i T_i κ_tot`. The terminal states are `aborted`, `returned v` (the stopping rule
  `M_S = 0` of steps 1 and 4) and `final S` (the loop is left for step 5 with support `S`); they are
  fixed points.
* Step 4's least-squares routine aborts exactly when `A_S^*A_S` is singular (proof of Lemma 14,
  p.30); otherwise it returns `C_S = fit X U S` and `M_S = Mval X U S σ̄`.
* Step 2 follows §6.1 (Theorem 15's algorithm): abort if `κ < 1`, `T < T_min` or `κ_tot + κ > K`.
  Algorithm 1 (p.15) has an extra "abort if T ≤ 0"; on every reachable state `T > 0` anyway.
* Call `i` *succeeds* (p.35) when its outcome is `some L` with
  `{f : |(X̂ − C_{S_i})(f)| ≥ T_i} ⊆ L ⊆ {f : |(X̂ − C_{S_i})(f)| > T_i/2}`.
* The final estimator uses `r_c` groups of `v_c` points, stored as one sample of `r_c·v_c` points
  (point `(i, j)` at index `finProdFinEquiv (i, j)`). `⌈log(17s/δ_est)⌉ = ⌈log₂(510 s)⌉ =
  Nat.clog 2 (510 s)`.
* (50): `K′ = 2^{⌈log K⌉}`, `W_{K′} = {2^i : i ≤ ⌈log K⌉}`, `A₀ = 128`, `C₀ = 2^{30}`, `θ = 2^{−28}`,
  `log N = a·d`; `D`, `ϕ_max` from (19) and `q_v` from (21), evaluated at `κ = K`.
-/

/-- The work budget `K = 31000 s`. -/
def Kbud (s : ℕ) : ℕ := 31000 * s

/-- A state of the support-identification loop. -/
inductive LoopState (a d : ℕ) where
  /-- At step 2 of a round, with support `S`, threshold `T` and cumulative ratio `κ_tot`. -/
  | running (S : Finset (G a d)) (T κtot : ℝ)
  /-- The algorithm aborted. -/
  | aborted
  /-- The algorithm returned `v` by the stopping rule `M_S = 0`. -/
  | returned (v : G a d → ℂ)
  /-- The loop was left for the final coefficient estimation with support `S`. -/
  | final (S : Finset (G a d))

/-- Step 1 of §6.1: `S = ∅`, `C_∅ = 0`, `κ_tot = 0`; return `0` if `M_∅ = 0`, else `T = M_∅`. -/
noncomputable def loopInit {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ) :
    LoopState a d :=
  if Mval X U ∅ (Real.sqrt s * τ) = 0 then .returned 0
  else .running ∅ (Mval X U ∅ (Real.sqrt s * τ)) 0

/-- One round (steps 2–4 of §6.1) with locator outcome `L` for this round's call. -/
noncomputable def loopStep {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (L : Option (Finset (G a d))) : LoopState a d → LoopState a d
  | .running S T κtot =>
      let σbar := Real.sqrt s * τ
      let Tmin := τ / 2
      let κ := Mval X U S σbar ^ 2 / T ^ 2
      if κ < 1 ∨ T < Tmin ∨ (Kbud s : ℝ) < κtot + κ then .aborted else
      match L with
      | none => .aborted
      | some Lnew =>
          let S' := S ∪ Lnew
          if 17 * s ≤ S'.card then .aborted
          else if (gram U S').det = 0 then .aborted
          else
            let M' := Mval X U S' σbar
            if M' = 0 then .returned (fit X U S')
            else if T = Tmin then .final S'
            else .running S' (max Tmin (min (T / 2) M')) (κtot + κ)
  | other => other

/-- The loop state after step 1 (`i = 0`) and after round `i ≥ 1`, with call `i` returning
`loc i`. -/
noncomputable def loopAt {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) : ℕ → LoopState a d
  | 0 => loopInit X U s τ
  | i + 1 => loopStep X U s τ (loc (i + 1)) (loopAt X U s τ loc i)

/-- The support of a running state (`∅` otherwise). -/
def LoopState.supp {a d : ℕ} : LoopState a d → Finset (G a d)
  | .running S _ _ => S
  | _ => ∅

/-- The threshold of a running state (`0` otherwise). -/
def LoopState.thr {a d : ℕ} : LoopState a d → ℝ
  | .running _ T _ => T
  | _ => 0

/-- The cumulative ratio `κ_tot` of a running state (`0` otherwise). -/
def LoopState.tot {a d : ℕ} : LoopState a d → ℝ
  | .running _ _ κtot => κtot
  | _ => 0

/-- The state is `running`. -/
def LoopState.IsRunning {a d : ℕ} : LoopState a d → Prop
  | .running _ _ _ => True
  | _ => False

/-- Round `i` (`i ≥ 1`) is reached: the state after round `i − 1` is running. -/
def RoundReached {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : Prop :=
  1 ≤ i ∧ (loopAt X U s τ loc (i - 1)).IsRunning

/-- `S_i`, the support before call `i`. -/
noncomputable def roundS {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : Finset (G a d) :=
  (loopAt X U s τ loc (i - 1)).supp

/-- `T_i`, the threshold of call `i`. -/
noncomputable def roundT {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : ℝ :=
  (loopAt X U s τ loc (i - 1)).thr

/-- `κ_i = M_{S_i}² / T_i²`. -/
noncomputable def roundKappa {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : ℝ :=
  Mval X U (roundS X U s τ loc i) (Real.sqrt s * τ) ^ 2 / roundT X U s τ loc i ^ 2

/-- Call `i` is made: round `i` is reached and accepted by the checks of step 2
(`κ_i ≥ 1`, `T_i ≥ T_min`, `κ_tot + κ_i ≤ K`). -/
def CallMade {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : Prop :=
  RoundReached X U s τ loc i ∧
    ¬ (roundKappa X U s τ loc i < 1 ∨ roundT X U s τ loc i < τ / 2 ∨
      (Kbud s : ℝ) < (loopAt X U s τ loc (i - 1)).tot + roundKappa X U s τ loc i)

/-- Call `i` succeeds: it returns a list containing every `f` with `|R̂_i(f)| ≥ T_i` and only
frequencies with `|R̂_i(f)| > T_i/2`, where `R̂_i = X̂ − C_{S_i}`. -/
def CallSucceeds {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ)
    (loc : ℕ → Option (Finset (G a d))) (i : ℕ) : Prop :=
  let S := roundS X U s τ loc i
  let T := roundT X U s τ loc i
  ∃ L, loc i = some L ∧
    (∀ f, T ≤ ‖(hat X - fit X U S) f‖ → f ∈ L) ∧
    (∀ f ∈ L, T / 2 < ‖(hat X - fit X U S) f‖)

/-- `r_c = 2⌈log(17s/δ_est)⌉ + 1` with `δ_est = 1/30`. -/
def rc (s : ℕ) : ℕ := 2 * Nat.clog 2 (510 * s) + 1

/-- `v_c = ⌈16384 b_ls² s⌉`. -/
noncomputable def vc (s : ℕ) : ℕ := ⌈16384 * bls ^ 2 * (s : ℝ)⌉₊

/-- The residual signal (37): `R(t) = X(t) − Σ_{f∈S} C_S(f) χ_f(t)`. -/
noncomputable def residual {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (S : Finset (G a d))
    (t : G a d) : ℂ :=
  X t - ∑ f ∈ S, fit X U S f * chi f t

/-- The final coefficient estimate of §6.3: group means `μ_i(f)` of `R(t_{i,j})·conj(χ_f(t_{i,j}))`
over `v_c` points, coordinatewise median `λ(f)` over the `r_c` groups, `X̃(f) = λ(f) + C_S(f)` on
`S` and `0` off `S`. -/
noncomputable def finalEstimate {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ)
    (S : Finset (G a d)) (pts : Fin (rc s * vc s) → G a d) : G a d → ℂ := by
  classical exact fun f =>
    if f ∈ S then
      cmedian (fun i : Fin (rc s) =>
        (1 / (vc s : ℂ)) * ∑ j : Fin (vc s),
          residual X U S (pts (finProdFinEquiv (i, j))) *
            (starRingEnd ℂ) (chi f (pts (finProdFinEquiv (i, j))))) + fit X U S f
    else 0

/-- `ϕ_max = (3κ log N / γ)^{1/4}` (19), with `log N` given as `L`. -/
noncomputable def phiMax (κ L γ : ℝ) : ℝ := (3 * κ * L / γ) ^ (1 / 4 : ℝ)

/-- The cutoff `D = (42 κ log N / (θ γ)) ϕ_max` (19), `θ = 2^{−28}`. -/
noncomputable def Dcut (κ L γ : ℝ) : ℝ := 42 * κ * L / ((2 : ℝ) ^ (-28 : ℤ) * γ) * phiMax κ L γ

/-- `q_v = 8⌈log(3D/γ)⌉ + 1` (21). -/
noncomputable def qv (κ L γ : ℝ) : ℕ := 8 * ⌈Real.logb 2 (3 * Dcut κ L γ / γ)⌉₊ + 1

/-- The total number of query occurrences (50):
`Q_total = n_ls + Q_node + 2048 K q* + r_c v_c`, `Q_node = 15 C₀ (log N) Σ_{w∈W_{K′}} w⌈2A₀K/w⌉`,
`q* = q_v(K)`, `γ = 1/(30K)`, `log N = a·d`. -/
noncomputable def Qtotal (s a d : ℕ) : ℕ :=
  let K := Kbud s
  let γ : ℝ := 1 / (30 * (K : ℝ))
  let Qnode := 15 * 2 ^ 30 * (a * d) *
    ∑ i ∈ Finset.range (Nat.clog 2 K + 1), 2 ^ i * ⌈(2 * 128 * (K : ℝ)) / (2 : ℝ) ^ i⌉₊
  nls s + Qnode + 2048 * K * qv K (a * d) γ + rc s * vc s

end NonadaptiveSFT


