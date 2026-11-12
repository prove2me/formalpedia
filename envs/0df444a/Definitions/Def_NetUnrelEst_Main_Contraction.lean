-- Prove2me | Definitions.Def_NetUnrelEst_Main_Contraction
-- name    : NetUnrelEst_Main_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:14:04.136052+00:00
-- url     : https://prove2.me/theorems/137118cd-a2ba-4ad0-adc0-37907832c5bf
-- title:
--   The contraction experiment, observation of working edges, and the random multiplicity representation
-- statement:
--   **Contraction experiment.** Each edge $e$ receives an independent exponential arrival time $T_e$ of rate $w_e=-\log p_e$; it has arrived (is connected) by time $t$ with probability $1-p_e^{t}$. So $(V,\{e:T_e\le t\})$ has the law of the working graph when $e$ fails with probability $p_e^{t}$. $K_t$ is its number of components, and
--   $$F(t)=\mathbb E(K_t-1),\qquad \zeta=-2\log(1-u).$$
--
--   **Observing working edges.** For failure bits with probabilities $p_e$, let $O$ be the set of edges observed working by time $t$: edge $e$ stays unobserved with probability $p_e^{t}$, independently; given $O$, observed edges work and an unobserved edge fails with probability $p_e^{1-t}$. Then $\|T_tf\|_2^2=\mathbb E[\mathbb E(f\mid O)^2]$, and $\|f\|_r^r=\mathbb E f^r$ under the product law of the failure bits. A function $f$ of the failure set is **increasing** when it is nondecreasing in the set of failed edges.
--
--   **Random multiplicities (§2.6).** Fix $0<\eta<1$ and $\pi=1-\eta$. For $0<p\le1$, $k=\lfloor\log p/\log\pi\rfloor$ satisfies $\pi^{k+1}<p\le\pi^k$; write $p=\pi^k y$. The multiplicity $N$ is $k+1$ with probability $(1-y)/(1-\pi)$ and $k$ otherwise, and $Z=\pi^N$. A deterministic working bit ($p=0$) is not represented ($Z=0$). The light-edge counts followed by observations through time $t$ give
--   $$\mathbb E\big[\mathbb E(f\mid S_t)^2\big]=\mathbb E_N\Big[\mathbb E\big[\mathbb E(f\mid O)^2\,\big|\,N\big]\Big],$$
--   the ordinary observation experiment run with failure probabilities $Z_e$ after the counts are drawn.
--
--   **Formalization Note.** All expectations are finite sums over failure sets (`expect` of the reused model). Powers are `Real.rpow`, with $0^0=1$, so at $t=0$ nothing is observed. The multiplicity law of a set $U$ of edges taking $k_e+1$ is the product law with probabilities $(1-y_e)/(1-\pi)$.
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 8, §2.1; pp. 10–11, §2.4; p. 12, §2.6; p. 32, App. A; pp. 33–34, App. B

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model

open scoped BigOperators Classical

noncomputable section

namespace NetUnrelEst.Main

open NetUnrelDesign.Main

/-!
# The contraction experiment, observation of working edges, and the multiplicity representation

Mu-Xia Sun, *Near-Linear Estimation of Network Unreliability* (STOC 2027 submission),
doi:10.5281/zenodo.23913531, §2.1 (p. 8), §2.4 (pp. 10–11), §2.6 (p. 12), App. A (p. 32),
App. B (pp. 33–34).

**Contraction experiment.** Edge `e` gets an independent exponential arrival time `T_e` of rate
`w_e = −log p_e`; it has arrived by time `t` with probability `1 − p_e^t`. The graph
`(V, {e : T_e ≤ t})` therefore has the law of the working graph when edge `e` fails with
probability `p_e^t` (`atTime p t`). `K_t` is its number of components, `meanK = E K_t`, and
`Fcomp = F(t) = E(K_t − 1)`. `zeta u = ζ = −2 log(1 − u)`.

**Observations.** For failure bits with failure probabilities `p`, the edges observed working by
time `t` form a random set `O`: edge `e` is unobserved with probability `p_e^t`, independently;
given `O`, an observed edge works and an unobserved edge fails with probability `p_e^{1−t}`.
`obsSecondMoment a b f = E[E(f | O)²]` for an experiment in which edge `e` is unobserved with
probability `a_e` and, if unobserved, fails with conditional probability `b_e`; the ordinary
observation through time `t` is `a = p^t`, `b = p^{1−t}` (`ordObsSecondMoment`, which is
`‖T_t f‖₂²`). `lpNormPow p f r = E[f^r]` under the product law of the failure bits, so
`‖f‖_r = (lpNormPow p f r)^{1/r}` for `f ≥ 0`. `IsIncreasing f`: `f` is nondecreasing in the set
of failed edges.

**Multiplicity representation (§2.6).** `piOf η = π = 1 − η`. For failure probability `0 < p ≤ 1`
the adjacent integers are `k = adjK η p = ⌊log p / log π⌋` and `k + 1`, so that
`π^{k+1} < p ≤ π^k`; `N = k + 1` with probability `upProb η p = (1 − y)/(1 − π)`, `p = π^k y`, and
`N = k` otherwise; `Z = π^N`. A deterministic working bit (`p = 0`) is not represented: `Z = 0`.
For the set `U` of edges that take `k + 1`, `repCount η p U e = N_e` and `repZ η p U e = Z_e`.
The light-edge counts followed by
observations through time `t` (`S_t`) give `repObsSecondMoment η p t f = E[E(f | S_t)²]`: the
counts are drawn first (`U` with independent probabilities `upProb`), then the ordinary
observation experiment runs with failure probabilities `Z`.
-/

/-- Failure probabilities `p_e^t`: edge `e` has not arrived by time `t`. -/
def atTime {m : ℕ} (p : Fin m → ℝ) (t : ℝ) : Fin m → ℝ := fun e => p e ^ t

/-- `E K_t`: the mean number of components of `(V, {e : T_e ≤ t})`. -/
def meanK {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (t : ℝ) : ℝ :=
  expect (atTime p t) fun F => (numComponents ends F : ℝ)

/-- `F(t) = E(K_t − 1)`. -/
def Fcomp {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (t : ℝ) : ℝ :=
  expect (atTime p t) fun F => (numComponents ends F : ℝ) - 1

/-- `ζ = −2 log(1 − u)`. -/
def zeta (u : ℝ) : ℝ := -2 * Real.log (1 - u)

/-- `f` is nondecreasing in the set of failed edges. -/
def IsIncreasing {m : ℕ} (f : Finset (Fin m) → ℝ) : Prop :=
  ∀ F F' : Finset (Fin m), F ⊆ F' → f F ≤ f F'

/-- `E[f^r]` under independent failure probabilities `p` (so `‖f‖_r = (E f^r)^{1/r}` for `f ≥ 0`). -/
def lpNormPow {m : ℕ} (p : Fin m → ℝ) (f : Finset (Fin m) → ℝ) (r : ℝ) : ℝ :=
  expect p fun F => f F ^ r

/-- `E[E(f | O)²]`: edge `e` is unobserved with probability `a e`; an observed edge works, an
unobserved edge fails with conditional probability `b e`. -/
def obsSecondMoment {m : ℕ} (a b : Fin m → ℝ) (f : Finset (Fin m) → ℝ) : ℝ :=
  expect (fun e => 1 - a e) fun O =>
    (expect (fun e => if e ∈ O then 0 else b e) f) ^ 2

/-- `‖T_t f‖₂² = E[E(f | O_t)²]` for ordinary observation of working edges through time `t`. -/
def ordObsSecondMoment {m : ℕ} (p : Fin m → ℝ) (t : ℝ) (f : Finset (Fin m) → ℝ) : ℝ :=
  obsSecondMoment (fun e => p e ^ t) (fun e => p e ^ (1 - t)) f

/-- `π = 1 − η`. -/
def piOf (η : ℝ) : ℝ := 1 - η

/-- The lower adjacent integer `k = ⌊log p / log π⌋`, so that `π^{k+1} < p ≤ π^k` for `0 < p ≤ 1`. -/
def adjK (η p : ℝ) : ℕ := ⌊Real.log p / Real.log (piOf η)⌋₊

/-- The probability of choosing `k + 1`: `(1 − y)/(1 − π)` with `p = π^k y`; `0` for `p = 0`. -/
def upProb (η p : ℝ) : ℝ :=
  if p = 0 then 0 else (1 - p / piOf η ^ adjK η p) / (1 - piOf η)

/-- The multiplicity `N_e = k_e + 1{e ∈ U}`. -/
def repCount {m : ℕ} (η : ℝ) (p : Fin m → ℝ) (U : Finset (Fin m)) (e : Fin m) : ℕ :=
  adjK η (p e) + if e ∈ U then 1 else 0

/-- `Z_e = π^{N_e}` when the edges in `U` take `k_e + 1` and the others `k_e`; `0` for `p_e = 0`. -/
def repZ {m : ℕ} (η : ℝ) (p : Fin m → ℝ) (U : Finset (Fin m)) (e : Fin m) : ℝ :=
  if p e = 0 then 0 else piOf η ^ (adjK η (p e) + if e ∈ U then 1 else 0)

/-- `E[E(f | S_t)²]` for the light-edge counts followed by observations through time `t`. -/
def repObsSecondMoment {m : ℕ} (η : ℝ) (p : Fin m → ℝ) (t : ℝ) (f : Finset (Fin m) → ℝ) : ℝ :=
  expect (fun e => upProb η (p e)) fun U => ordObsSecondMoment (repZ η p U) t f

end NetUnrelEst.Main


