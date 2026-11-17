-- Prove2me | Definitions.Def_PrefixVR_Supplement_Sample2
-- name    : PrefixVR_Supplement_Sample2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:50:32.25936+00:00
-- url     : https://prove2.me/theorems/170f21d8-e0ae-4b0d-8ef1-159be70e3080
-- title:
--   Sample space and expectation of Algorithm 2
-- statement:
--   The **sample space of Algorithm 2** with batch size $b$ and horizon $T$: an outcome consists of the output index $\tau\in[T]$ and, for every update $t\le T$, $b$ prefix draws in $A_{r-1}=[k_r]$ and $b$ active draws in $[n]$. The expectation $\mathbb E$ over all randomness of the algorithm is the uniform average over this finite set,
--   $$
--   \mathbb E[X]=\frac1{|\Omega|}\sum_{\omega\in\Omega}X(\omega),
--   $$
--   which is the product of the uniform laws: all draws are independent and uniform, each batch i.i.d. with replacement, and $\tau$ independent of them, as §6 and §3 prescribe.
--
--   **Formalization Note** When $k_r=0$ the prefix coordinates are one-point dummies and at $r=q$ the active coordinates are drawn but unused; unused independent coordinates change no expectation. Indices are 0-based (`Fin`).
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §6, p.9 (draws of (19)–(20)); Algorithm 2, line 2, p.10; §3, p.4 (independence)

import Mathlib
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Supplement_step2

namespace PrefixVR.Supplement

open PrefixVR

/-- The number of values of each prefix draw at update `t` of Algorithm 2: `j_{t,ℓ} ∼ Unif(A_{r−1})`
has `k_r = |A_{r−1}|` values (§6, p.9). When `k_r = 0` nothing is drawn; a one-point dummy is
used. -/
noncomputable def pCard (n b t : ℕ) : ℕ := max (blockEnd n b (cyclePos (numBlocks n b) t - 1)) 1

/-- **The sample space of Algorithm 2 with batch size `b` and horizon `T`.**
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), §6, p.9: "After choosing `x_{t+1}`,
draw `j_{t,1}, …, j_{t,b}` independently and uniformly from `A_{r−1}`, when this set is nonempty
… For `r < q`, independently draw `i_{t,1}, …, i_{t,b} ∼ Unif([n])` with replacement"; Algorithm 2,
line 2: "draw `τ ∼ Unif([T])`"; §3, p.4: the draws are fresh and independent and `τ` is
independent of the estimator samples.

An outcome is `(τ − 1, (j_{t,·} − 1, i_{t,·} − 1)_{t=1}^T)`: the output index and, for each update
`t = k + 1`, the `b` prefix draws in `[k_r]` and the `b` active draws in `[n]`. The law is the
uniform law on this finite set (see `expect2`), i.e. the product of the uniform laws: all draws
are independent and uniform, the batches i.i.d. with replacement.

**Formalization Note.** When `k_r = 0` the prefix coordinates are one-point dummies and when
`r = q` the active coordinates are drawn but unused; unused independent coordinates change no
expectation. Indices are 0-based (`Fin`). -/
abbrev Sample2 (n b T : ℕ) : Type :=
  Fin T × ((k : Fin T) → (Fin b → Fin (pCard n b (k.val + 1))) × (Fin b → Fin n))

/-- The output index `τ ∈ {1, …, T}` of an outcome (Algorithm 2, line 2, p.10). -/
def tau2 {n b T : ℕ} (ω : Sample2 n b T) : ℕ := ω.1.val + 1

/-- The draws of an outcome as a sequence: `drawSeq2 ω k` is the pair (prefix draws, active
draws) of update `t = k + 1 ≤ T`, and an unused default beyond the horizon. -/
def drawSeq2 {n b T : ℕ} [NeZero n] (ω : Sample2 n b T) (k : ℕ) :
    (Fin b → ℕ) × (Fin b → Fin n) :=
  if hk : k < T then (fun ℓ => (((ω.2 ⟨k, hk⟩).1 ℓ : Fin _) : ℕ), (ω.2 ⟨k, hk⟩).2)
  else (fun _ => 0, fun _ => Fin.ofNat n 0)

/-- **Expectation over all randomness of Algorithm 2**: the uniform average
`𝔼[F] = |Ω|⁻¹ ∑_{ω ∈ Ω} F(ω)` over `Ω = Sample2 n b T` (the output index and all batch draws).

**Formalization Note.** The joint law of independent uniform draws on finite sets is the uniform
law on their product. For `T ≥ 1`, `n ≥ 1` the set is nonempty. -/
noncomputable def expect2 {n b T : ℕ} (F : Sample2 n b T → ℝ) : ℝ :=
  (Fintype.card (Sample2 n b T) : ℝ)⁻¹ * ∑ ω, F ω

end PrefixVR.Supplement


