-- Prove2me | Definitions.Def_FreeOrderEPTAS_Schedule
-- name    : FreeOrderEPTAS_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:08.297096+00:00
-- url     : https://prove2.me/theorems/f43feab8-2d35-42e9-9ec2-6a6116da50ae
-- title:
--   The standing situation of §3.5
-- statement:
--   The hypotheses of the value analysis: $\sigma^*$ is optimal, $1/\epsilon$ is a positive integer, $E\in[(1-\epsilon)\mathrm{OPT},\mathrm{OPT}]$, the guesses satisfy (14) and (15), and $x$ is the assignment of Corollary 3.3: cardinality-feasible, with $\sum_j\ell_{ij}x_{ij}\ge(1-\epsilon)\mathrm{DeltaGuess}(B_i)$ on every machine.
--
--   `IsFirstAhead` says that $t$ is the minimal time when $\sigma$ is ahead of schedule, with $X_{\sigma(t)}$ on machine $i$: $R_{t+1}\ge\mathrm{BaseGuess}(B_i)$, while every earlier time is assigned and has $R_{t'+1}<\mathrm{BaseGuess}$ of its machine.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.5, pp.20–22; hypotheses of Corollary 3.3, p.20

import Mathlib
import Definitions.Def_FreeOrderEPTAS_IsGuess
import Definitions.Def_FreeOrderEPTAS_IPProphets
import Definitions.Def_FreeOrderEPTAS_OPT

namespace FreeOrderEPTAS

variable {n : ℕ}

/-- The standing situation of §3.5 (arXiv:2007.13121v3, pp.20–22): `σ*` is optimal, `1/ϵ` is an
integer, the estimate is `E ∈ [(1 - ϵ) OPT, OPT]`, the guesses satisfy (14), (15), and `x` is the
assignment of Corollary 3.3: cardinality-feasible, with load `∑_j ℓ_ij x_ij ≥ (1 - ϵ) DeltaGuess(B_i)`
on every machine. -/
structure Schedule (I : Instance n) (σs : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σs ϵ + 1) → ℝ) (x : Assignment (2 * numJumps I σs ϵ + 1) n) :
    Prop where
  /-- `σ*` is optimal. -/
  optimal : V I σs = OPT I
  /-- `1/ϵ` is a positive integer. -/
  inv_int : ∃ q : ℕ, 0 < q ∧ ϵ = 1 / (q : ℝ)
  /-- `E ≥ (1 - ϵ) OPT`. -/
  est_lower : (1 - ϵ) * OPT I ≤ E
  /-- `E ≤ OPT`. -/
  est_upper : E ≤ OPT I
  /-- Inequalities (14), (15). -/
  guess : IsGuess I σs ϵ E b Δ
  /-- `x` is cardinality-feasible. -/
  card : ProphetCard x
  /-- The load of Corollary 3.3. -/
  load : ∀ i, (1 - ϵ) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)

/-- `t` is the minimal time when `σ` is ahead of schedule (p.20), with `X_{σ(t)}` assigned to
machine `i`: `R_{t+1} ≥ BaseGuess(B_i)`, and every earlier time is assigned and behind schedule. -/
def IsFirstAhead (I : Instance n) (σ : Equiv.Perm (Fin n)) {m : ℕ} (b : Fin m → ℝ)
    (x : Assignment m n) (t : Fin n) (i : Fin m) : Prop :=
  x i (σ t) = true ∧ b i ≤ R I σ (t.val + 1) ∧
    ∀ t' : Fin n, t' < t → ∃ i', x i' (σ t') = true ∧ R I σ (t'.val + 1) < b i'

end FreeOrderEPTAS


