-- Prove2me | Definitions.Def_ParallelLpSCO_EpochDA_Algorithms
-- name    : ParallelLpSCO_EpochDA_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:04:31.891149+00:00
-- url     : https://prove2.me/theorems/5fed93de-f96e-458a-80a4-2f414f3351f2
-- title:
--   Algorithm 9 (ParallelEpochDA), Algorithm 11 (Aggregate) and Algorithm 8 (p-MorGradEst) as printed
-- statement:
--   **Algorithm 9 (ParallelEpochDA, p. 61)**, input $\bar x$, $r=\rho>0$, $\lambda,\phi>0$, $L$, and $C_p\ge\frac{2\cdot4^p2^{p-1}3^p}{(2^{2-p})^2(2^{p-1}-1)}$ (`alg9CpMin`):
--   - $\eta_1=\frac{2^{2-p}}{4^{p-1}\lambda}$, $T_1=\lceil 4^p/(2^{2-p})^2\rceil$, $T=\lceil C_pL^p/(\lambda\phi^{p-1})\rceil$;
--   - $\xi_i\sim GG_p(0,\rho^2I_d)$ for $i\in[2T]$, and $g(\bar x+\xi_i)$ queried in one parallel round;
--   - $x^0_1=\bar x$, $k=1$; while $\sum_{j\le k}T_j\le T$: $x^1_k=x^0_k$, $\Phi_k=\|\cdot-x^0_k\|_p^p/p$, and for $t\in[T_k]$, with $i=\sum_{j<k}T_j+t$,
--   $$x^{t+1}_k=\operatorname*{argmin}_{x\in B_p(\bar x,r)}\Big\{\eta_k\big\langle\tfrac{\gamma_{\rho,p}(x^t_k-\bar x-\xi_i)}{\gamma_{\rho,p}(\xi_i)}g(\bar x+\xi_i),x\big\rangle+\tfrac{\eta_k\lambda}p\|x-\bar x\|_p^p+D_{\Phi_k}(x,x^t_k)\Big\};$$
--   - then $x^0_{k+1}=\frac1{T_k}\sum_{t=1}^{T_k}x^{t+1}_k$, $T_{k+1}=\lceil2^{p-1}T_k\rceil$, $\eta_{k+1}=\eta_k/2^{p-1}$, $k\leftarrow k+1$;
--   - return $x^0_k$.
--
--   In Lean, `epochLen p k` $=T_k$, `epochEta p λ k` $=\eta_k$, `cumLen p k` $=\sum_{j=1}^kT_j$, `alg9Start … k` $=x^0_k$, `alg9FinalEpoch` is the least $k\ge1$ with $\sum_{j\le k}T_j>T$, and `alg9Output` $=x^0_K$. `alg9Updates` $=\sum_{j<K}T_j$ counts the proximal updates of line 11, and `alg9Queries` $=2T$. The random inputs are a sequence $(\xi_i,U_i)_{i\ge1}$, i.i.d. with law $GG_p(0,r^2)\otimes\mathrm{Unif}[0,1]$ (`IsAlg9SampleLaw`), and the $i$-th answer is $g(\bar x+\xi_i,U_i)$.
--
--   **Algorithm 11 (Aggregate, p. 93).** Given $y_1,\dots,y_k$ and $R$, return the first $y_i$ such that at least $0.51k$ points $y_j$ satisfy $\|y_i-y_j\|_p\le 2R/3$ (`none` if there is none). `aggregateDistances` counts the pairwise distances evaluated: $k$ for every index scanned.
--
--   **Algorithm 8 (p-MorGradEst, p. 51)**, given an $r$-BROO $O_{\lambda,\delta}(\cdot)$, $y$, $\lambda$, $T_0$, $j_{\max}$:
--   - $\delta_j=r/(2^jT_0)^{1/p}$, $x_j=O_{\lambda,\delta_j}(y)$, $g_j=\lambda J_p(y-x_j)$;
--   - draw $J\sim\mathrm{Geom}(1/2)$ on $\{1,2,\dots\}$;
--   - return $\hat g=g_0+2^J(g_J-g_{J-1})$ if $J\le j_{\max}$, and $\hat g=g_0$ otherwise.
--
--   `geomHalf` is the law $P(J=j)=2^{-j}$, $j\ge1$.
--
--   **Formalization Note.** Epochs and samples are numbered from $1$ as in the paper. The argmin of line 11 (unique, by strict convexity on a compact ball) is a Hilbert-ε choice. `alg9FinalEpoch` is an `sInf` over a set that is nonempty because $T_j\ge1$. Algorithm 8's $T_0$ and $j_{\max}$ (line 2–3) are parameters here; Lemma 22 quantifies over them.
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 61 (Algorithm 9), p. 93 (Algorithm 11), p. 51 (Algorithm 8), p. 5 (Geom)

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics

open MeasureTheory

/-!
# Algorithm 9 (ParallelEpochDA), Algorithm 11 (Aggregate), Algorithm 8 (p-MorGradEst)

Nie, Shyam, Bullins, *Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in
ℓp Geometries*, STOC 2027 submission (manuscript, sha256 fe68639b…): Algorithm 9 p. 61,
Algorithm 11 p. 93, Algorithm 8 p. 51.

Algorithm 9 is written as the paper prints it, as a function of its random inputs: the samples
`ξ_i ∼ GG_p(0, ρ²)` (line 3) and the oracle's answers `a_i = g(x̄ + ξ_i)` (line 4), indexed by
`i = 1, 2, …`. Its input requires `r = ρ`, so one radius `r` serves both. Epochs and samples are
numbered from `1` as in the paper.
-/

namespace ParallelLpSCO.EpochDA

/-! ## Algorithm 9 (ParallelEpochDA, p. 61) -/

/-- `T₁ = ⌈4^p / (2^{2−p})²⌉` (line 2). -/
noncomputable def alg9T1 (p : ℝ) : ℕ :=
  ⌈(4 : ℝ) ^ p / ((2 : ℝ) ^ (2 - p)) ^ 2⌉₊

/-- `η₁ = 2^{2−p} / (4^{p−1} λ)` (line 2). -/
noncomputable def alg9Eta1 (p lam : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 - p) / ((4 : ℝ) ^ (p - 1) * lam)

/-- The query budget `T = ⌈C_p L^p / (λ ϕ^{p−1})⌉` (line 2). -/
noncomputable def alg9T (p L lam phi Cp : ℝ) : ℕ :=
  ⌈Cp * L ^ p / (lam * phi ^ (p - 1))⌉₊

/-- The lower bound `2 · 4^p 2^{p−1} 3^p / ((2^{2−p})² (2^{p−1} − 1))` that line 2 requires of
`C_p`. -/
noncomputable def alg9CpMin (p : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ p * (2 : ℝ) ^ (p - 1) * (3 : ℝ) ^ p /
    (((2 : ℝ) ^ (2 - p)) ^ 2 * ((2 : ℝ) ^ (p - 1) - 1))

/-- Epoch lengths: `epochLen p k = T_k` for `k ≥ 1`, with `T_{k+1} = ⌈2^{p−1} T_k⌉`
(line 13). -/
noncomputable def epochLen (p : ℝ) (k : ℕ) : ℕ :=
  (fun T : ℕ => ⌈(2 : ℝ) ^ (p - 1) * T⌉₊)^[k - 1] (alg9T1 p)

/-- Step sizes: `epochEta p λ k = η_k = η₁ / (2^{p−1})^{k−1}` for `k ≥ 1` (line 13). -/
noncomputable def epochEta (p lam : ℝ) (k : ℕ) : ℝ :=
  alg9Eta1 p lam / ((2 : ℝ) ^ (p - 1)) ^ (k - 1)

/-- `S_k = ∑_{j=1}^{k} T_j`, the number of samples used by epochs `1, …, k`. -/
noncomputable def cumLen (p : ℝ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, epochLen p j

/-- One dual-averaging step (lines 10–11): from `x^t_k`, with sample `ξ_i` and answer `a_i`,
`x^{t+1}_k ∈ argmin_{x ∈ B_p(x̄, r)} {η ⟨∇̃, x⟩ + (ηλ/p)‖x − x̄‖_p^p + D_{Φ_k}(x, x^t_k)}`, where
`∇̃ = (γ_{r,p}(x^t_k − x̄ − ξ_i)/γ_{r,p}(ξ_i)) a_i` and `Φ_k = ‖· − x^0_k‖_p^p / p`. The minimizer
exists and is unique. -/
noncomputable def alg9Step {d : ℕ} (p r lam eta : ℝ) (xbar x0 xt ξi ai : Vec d) : Vec d :=
  let est := pgreg p r xbar xt ξi ai
  let obj := fun x : Vec d =>
    eta * ∑ j, est j * x j + eta * lam / p * lpNorm p (x - xbar) ^ p + bregman p x0 x xt
  Classical.epsilon fun x => x ∈ lpBall p xbar r ∧ ∀ y ∈ lpBall p xbar r, obj x ≤ obj y

/-- Within epoch `k` started at `x0 = x^0_k`: `alg9Inner … k x0 t = x^{t+1}_k`, so
`x^1_k = x^0_k` (line 7) and step `t` uses sample index `S_{k−1} + t` (line 9). -/
noncomputable def alg9Inner {d : ℕ} (p r lam : ℝ) (xbar : Vec d) (ξ a : ℕ → Vec d) (k : ℕ)
    (x0 : Vec d) : ℕ → Vec d
  | 0 => x0
  | t + 1 =>
      alg9Step p r lam (epochEta p lam k) xbar x0 (alg9Inner p r lam xbar ξ a k x0 t)
        (ξ (cumLen p (k - 1) + (t + 1))) (a (cumLen p (k - 1) + (t + 1)))

/-- The average `x^0_{k+1} = (1/T_k) ∑_{t=1}^{T_k} x^{t+1}_k` closing epoch `k` (line 13). -/
noncomputable def alg9EpochAvg {d : ℕ} (p r lam : ℝ) (xbar : Vec d) (ξ a : ℕ → Vec d) (k : ℕ)
    (x0 : Vec d) : Vec d :=
  ((epochLen p k : ℝ))⁻¹ • ∑ t ∈ Finset.Icc 1 (epochLen p k), alg9Inner p r lam xbar ξ a k x0 t

/-- `alg9StartAux … m = x^0_{m+1}`. -/
noncomputable def alg9StartAux {d : ℕ} (p r lam : ℝ) (xbar : Vec d) (ξ a : ℕ → Vec d) :
    ℕ → Vec d
  | 0 => xbar
  | m + 1 => alg9EpochAvg p r lam xbar ξ a (m + 1) (alg9StartAux p r lam xbar ξ a m)

/-- The epoch starting points: `alg9Start … k = x^0_k` for `k ≥ 1`; `x^0_1 = x̄` (line 5). -/
noncomputable def alg9Start {d : ℕ} (p r lam : ℝ) (xbar : Vec d) (ξ a : ℕ → Vec d) (k : ℕ) :
    Vec d :=
  alg9StartAux p r lam xbar ξ a (k - 1)

/-- The epoch at which the loop of lines 6–14 stops: the least `k ≥ 1` with `S_k > T`. -/
noncomputable def alg9FinalEpoch (p L lam phi Cp : ℝ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ alg9T p L lam phi Cp < cumLen p k}

/-- The output `x^0_K` of Algorithm 9 (line 15). -/
noncomputable def alg9Output {d : ℕ} (p r lam phi L Cp : ℝ) (xbar : Vec d) (ξ a : ℕ → Vec d) :
    Vec d :=
  alg9Start p r lam xbar ξ a (alg9FinalEpoch p L lam phi Cp)

/-- The number of Bregman proximal updates (line 11) Algorithm 9 performs: `S_{K−1}`. -/
noncomputable def alg9Updates (p L lam phi Cp : ℝ) : ℕ :=
  cumLen p (alg9FinalEpoch p L lam phi Cp - 1)

/-- The number of oracle queries Algorithm 9 makes: `2T`, all in one parallel round (line 4). -/
noncomputable def alg9Queries (p L lam phi Cp : ℝ) : ℕ :=
  2 * alg9T p L lam phi Cp

/-- The random inputs of Algorithm 9 on `(Ω, P)`: `(ξ_i, U_i)_{i ≥ 1}` independent, each with
law `GG_p(0, r²) ⊗ Unif[0, 1]`; the oracle answer to query `i` is `g(x̄ + ξ_i, U_i)`. -/
def IsAlg9SampleLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p r : ℝ) (P : Measure Ω)
    (ξ : ℕ → Ω → Vec d) (U : ℕ → Ω → unitInterval) : Prop :=
  (∀ i, Measurable fun ω => (ξ i ω, U i ω)) ∧
    ProbabilityTheory.iIndepFun (fun i ω => (ξ i ω, U i ω)) P ∧
    ∀ i, P.map (fun ω => (ξ i ω, U i ω)) = (ggLaw d p r).prod (volume : Measure unitInterval)

/-! ## Algorithm 11 (Aggregate, p. 93) -/

open Classical in
/-- `|{j ∈ [k] : ‖y_i − y_j‖_p ≤ 2R/3}|`. -/
noncomputable def aggCount {d k : ℕ} (p : ℝ) (y : Fin k → Vec d) (R : ℝ) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun j => lpNorm p (y i - y j) ≤ 2 * R / 3).card

open Classical in
/-- Algorithm 11: the first index `i` (in the order `1, …, k`) such that at least `0.51k` points
`y_j` satisfy `‖y_i − y_j‖_p ≤ 2R/3`; `none` if the loop ends without returning. -/
noncomputable def aggregate {d k : ℕ} (p : ℝ) (y : Fin k → Vec d) (R : ℝ) : Option (Fin k) :=
  (List.finRange k).find? fun i => decide ((51 / 100 : ℝ) * k ≤ aggCount p y R i)

/-- The number of pairwise ℓp distances Algorithm 11 evaluates: `k` for each index it scans. -/
noncomputable def aggregateDistances {d k : ℕ} (p : ℝ) (y : Fin k → Vec d) (R : ℝ) : ℕ :=
  match aggregate p y R with
  | some i => ((i : ℕ) + 1) * k
  | none => k * k

/-! ## Algorithm 8 (p-MorGradEst, p. 51) -/

/-- `Geom(1/2)` on `{1, 2, …}`: `P(J = j) = 2^{−j}`. -/
noncomputable def geomHalf : Measure ℕ :=
  Measure.sum fun j : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) • Measure.dirac (j + 1)

/-- Algorithm 8, lines 3–13, given the level `J`, an `r`-BROO `O` (`O λ δ y`), the query point
`y`, `λ`, `T₀` and `j_max`: with `δ_j = r / (2^j T₀)^{1/p}`, `x_j = O_{λ,δ_j}(y)` and
`g_j = λ J_p(y − x_j)`, the estimate is `g_0 + 2^J (g_J − g_{J−1})` if `J ≤ j_max` and `g_0`
otherwise. -/
noncomputable def morGradEst {d : ℕ} (p r lam T0 : ℝ) (jmax : ℕ) (O : ℝ → ℝ → Vec d → Vec d)
    (y : Vec d) (J : ℕ) : Vec d :=
  let δ : ℕ → ℝ := fun j => r / ((2 : ℝ) ^ j * T0) ^ (1 / p)
  let gj : ℕ → Vec d := fun j => lam • Jp p (y - O lam (δ j) y)
  if J ≤ jmax then gj 0 + (2 : ℝ) ^ J • (gj J - gj (J - 1)) else gj 0

end ParallelLpSCO.EpochDA


