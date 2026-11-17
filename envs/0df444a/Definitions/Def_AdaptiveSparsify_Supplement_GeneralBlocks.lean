-- Prove2me | Definitions.Def_AdaptiveSparsify_Supplement_GeneralBlocks
-- name    : AdaptiveSparsify_Supplement_GeneralBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:51:28.100194+00:00
-- url     : https://prove2.me/theorems/6c311deb-1927-4262-9f72-18c011a358b3
-- title:
--   General block sizes: the hypotheses, input and success event of Theorem 2
-- statement:
--   The objects of Theorem 2 (general block sizes).
--
--   1. **Hypotheses.** For an ERM instance $\min\{c^\top x : x\in K_1\times\cdots\times K_m,\ A^\top x=b\}$ (the published `ERMInstance`) and parameters $\nu_1,\dots,\nu_m$, `GeneralAdmissible` collects every hypothesis of Theorem 1 as published, except the bound $n_i\le C_K$: $d\ge1$, $\kappa>0$, $n_i\ge1$; each $K_i\subseteq[-\kappa,\kappa]^{n_i}$ compact and convex; the entries of $A,b,c$ at most $\kappa$ in absolute value; $A^\top A\succeq\kappa^{-1}I$; a feasible $z$ with $B(z_i,1/\kappa)\subseteq K_i$ and given start points $w_i$ with $B(w_i,1/\kappa)\subseteq K_i$ (corrections C1 and C2 of Theorem 1). Block $i$ has a $\nu_i$-self-concordant barrier $\phi_i$.
--   2. **Input.** The memory layout of `ERMInstance` (the numbers $m,n,d,n_i$; the reals $A,b,c,w,\kappa,\varepsilon$), plus the indicator of the set $L$ of blocks to be carried exactly and the parameters $\nu_i$, stored right after $\varepsilon$.
--   3. **Time bound.** With $\nu=\sum_i\nu_i$ and $\nu_{\max}=\max_i\nu_i$,
--   $$C\Big(nd+M^4\nu\big(M^{\omega_0-1}+d\big)+\sqrt{\nu M}\Big(d^6+\sum_{i\in L}(n_i+d)^{\omega_0}\Big)\Big)\big(\log(n+d+\kappa+1/\varepsilon+\nu_{\max}+2)\big)^k .$$
--   4. **Success.** At some step the run has halted without fault within this bound, and its output $x$ satisfies $x_i\in K_i$ for all $i$, $A^\top x=b$, and $c^\top x\le\varepsilon+c^\top y$ for every feasible $y$.
--
--   These are the objects of Theorem 2, which removes the bound $n_i\le C_K$ of Theorem 1.
--
--   **Formalization Note** $\nu$ and $L$ are inputs because the step size $\eta=\varepsilon\alpha/(C_{\rm center}\sqrt\nu)$ of §6.4 needs $\nu$ and $L$ is chosen by the user. $M$ is not an input: it enters only the bound, which is increasing in $M$. The real suprema and sums are over the finite set of blocks.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 2, p.7; §6.4, pp.45–47; (2), p.4; Theorem 1, pp.6–7

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_AdaptiveSparsify_ERMInstance

namespace AdaptiveSparsify

/-!
# General block sizes: the hypotheses, input and success event of Theorem 2

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
Theorem 2 (General block sizes), p.7, proved in §6.4, pp.45–47.

**Formalization Note.**
* `GeneralAdmissible I ν` is every field of the published `ERMInstance.IsAdmissible` (Theorem 1's
  hypotheses with corrections C1, C2) except `dim_le` (`n_i ≤ C_K`), with the barrier of block `i` a
  `ν_i`-self-concordant barrier instead of a `C_K`-self-concordant one. Nothing else changes.
* Input. The memory of `ERMInstance` (integer cells `0, 1, 2, 3 + i`; real cells `A, b, c, w, κ, ε`),
  plus the indicator of `L` in integer cells `3 + m + i` (`1` if block `i ∈ L`, else `0`) and `ν_i`
  in real cell `n d + d + 2n + 2 + i`, right after `ε`. The step size `η = εα/(C_center √ν)` of §6.4,
  p.46, needs `ν`, and the set `L` of blocks carried exactly is chosen by the user, so both are inputs.
  `M` is not an input: it enters only the time bound, which is increasing in `M`.
* Time bound: `C (nd + M⁴ν(M^{ω₀−1} + d) + √(νM)(d⁶ + ∑_{i∈L}(n_i + d)^{ω₀})) ·
  (log(n + d + κ + 1/ε + ν_max + 2))^k` with `ν = ∑ ν_i`, `ν_max = max ν_i`: the `Õ` of Theorem 2
  hides only logs of `n, d, κ, 1/ε, max ν_i` (no `C_K`, no factor of `M`, `ν` or `n_i`).
* `ω₀` is any exponent achievable on the machine (`AdaptiveSparsify.Supplement.IsMatMulProgram`).
-/

namespace Supplement

open Matrix

/-- The hypotheses of Theorem 2: those of Theorem 1 (with C1, C2) except `n_i ≤ C_K`, block `i` having
a `ν_i`-self-concordant barrier. -/
structure GeneralAdmissible (I : ERMInstance) (ν : Fin I.blocks.m → ℝ) : Prop where
  d_pos : 1 ≤ I.d
  κ_pos : 0 < I.κ
  dim_pos : ∀ i, 1 ≤ I.blocks.dim i
  compact : ∀ i, IsCompact (I.K i)
  convex : ∀ i, Convex ℝ (I.K i)
  bounded : ∀ i, ∀ x ∈ I.K i, ∀ l, |x l| ≤ I.κ
  barrier : ∀ i, EntropicBarrier.Universal.IsNuSelfConcordantBarrier (I.K i) (I.φ i) (ν i)
  A_le : ∀ j k, |I.A j k| ≤ I.κ
  b_le : ∀ k, |I.b k| ≤ I.κ
  c_le : ∀ j, |I.c j| ≤ I.κ
  gram : LoewnerLE (I.κ⁻¹ • (1 : Matrix (Fin I.d) (Fin I.d) ℝ)) (I.Aᵀ * I.A)
  strictly_feasible : ∃ z : Fin I.blocks.n → ℝ, I.Aᵀ *ᵥ z = I.b ∧ ∀ i,
    Metric.closedBall (WithLp.toLp 2 (I.blocks.restrict z i)) I.κ⁻¹ ⊆ I.K i
  start : ∀ i, Metric.closedBall (WithLp.toLp 2 (I.blocks.restrict I.w i)) I.κ⁻¹ ⊆ I.K i

/-- The integer input memory of Theorem 2: that of `ERMInstance`, plus the indicator of `L` in cells
`3 + m + i`. -/
def generalIntMem (I : ERMInstance) (L : Finset (Fin I.blocks.m)) : ℤ → ℤ := fun a =>
  if h : 3 + (I.blocks.m : ℤ) ≤ a ∧ (a - 3 - I.blocks.m).toNat < I.blocks.m then
    (if (⟨(a - 3 - I.blocks.m).toNat, h.2⟩ : Fin I.blocks.m) ∈ L then 1 else 0)
  else I.intMem a

/-- The first real cell after `ε` in the layout of `ERMInstance`: `n d + d + 2n + 2`. -/
def nuOffset (I : ERMInstance) : ℕ := I.blocks.n * I.d + I.d + I.blocks.n + I.blocks.n + 2

/-- The real input memory of Theorem 2: that of `ERMInstance` with accuracy `ε`, plus `ν_i` in cell
`nuOffset + i`. -/
noncomputable def generalRealMem (I : ERMInstance) (ν : Fin I.blocks.m → ℝ) (ε : ℝ) : ℤ → ℝ :=
  fun a =>
    if h : (nuOffset I : ℤ) ≤ a ∧ a.toNat - nuOffset I < I.blocks.m then
      ν ⟨a.toNat - nuOffset I, h.2⟩
    else I.realMem ε a

/-- The run of `P` on the Theorem 2 input. -/
noncomputable def generalRun (P : Program) (I : ERMInstance) (ν : Fin I.blocks.m → ℝ)
    (L : Finset (Fin I.blocks.m)) (ε : ℝ) (ω : ℕ → ℝ) (t : ℕ) : State :=
  run P I.env ω (init (generalIntMem I L) (generalRealMem I ν ε)) t

/-- The time bound of Theorem 2:
`C (nd + M⁴ν(M^{ω₀−1} + d) + √(νM)(d⁶ + ∑_{i∈L}(n_i + d)^{ω₀})) (log(n + d + κ + 1/ε + ν_max + 2))^k`,
with `ν = ∑ ν_i` and `ν_max = max_i ν_i`. -/
noncomputable def generalBound (I : ERMInstance) (ν : Fin I.blocks.m → ℝ)
    (L : Finset (Fin I.blocks.m)) (M ε ω₀ C : ℝ) (k : ℕ) : ℝ :=
  C * ((I.blocks.n : ℝ) * I.d + M ^ 4 * (∑ i, ν i) * (M ^ (ω₀ - 1) + I.d) +
      Real.sqrt ((∑ i, ν i) * M) *
        ((I.d : ℝ) ^ 6 + ∑ i ∈ L, ((I.blocks.dim i : ℝ) + I.d) ^ ω₀)) *
    (Real.log ((I.blocks.n : ℝ) + I.d + I.κ + 1 / ε + (⨆ i, ν i) + 2)) ^ k

/-- The success event of Theorem 2: at some step the run has halted without fault within the bound,
and its output is feasible and `ε`-optimal against every feasible point. -/
def GeneralSuccess (P : Program) (I : ERMInstance) (ν : Fin I.blocks.m → ℝ)
    (L : Finset (Fin I.blocks.m)) (M ε ω₀ C : ℝ) (k : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    (generalRun P I ν L ε ω t).halted = true ∧
    (generalRun P I ν L ε ω t).faulted = false ∧
    ((generalRun P I ν L ε ω t).work : ℝ) ≤ generalBound I ν L M ε ω₀ C k ∧
    I.Feasible (I.output (generalRun P I ν L ε ω t)) ∧
    ∀ y, I.Feasible y → I.c ⬝ᵥ I.output (generalRun P I ν L ε ω t) ≤ ε + I.c ⬝ᵥ y

end Supplement

end AdaptiveSparsify


