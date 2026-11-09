-- Prove2me | Definitions.Def_RandomQueryXOR_successProb
-- name    : RandomQueryXOR_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:58:00.762636+00:00
-- url     : https://prove2.me/theorems/99dce497-2c7f-48ae-b1c5-6ba7590a2b17
-- title:
--   Success probability of a randomized branching program in the random query model
-- statement:
--   A **randomized branching program** of width $W$ and length $T$ is a probability distribution $\mu$ over deterministic layered programs. On an input $x\in\{0,1\}^\iota$ a program $P\sim\mu$ is drawn, indices $i_1,\dots,i_T$ are drawn i.i.d. uniformly from $\iota$, independently of $P$, and $P$ is run on the samples $(i_1,x(i_1)),\dots,(i_T,x(i_T))$; $A(x)$ is its output. For $F:\{0,1\}^\iota\to\{0,1\}$ the **probability of success on input $x$** is
--   $$
--   \Pr[A(x)=F(x)],
--   $$
--   over the program and the indices. The paper's success probability of the program is the minimum over all inputs, so "success probability at least $2/3$" means $\Pr[A(x)=F(x)]\ge 2/3$ for every $x$.
--
--   **Formalization Note** The per-node edge distributions of §3.1 (iii) fold into $\mu$: a run visits one node per layer, so independent edge choices at the nodes combined with the program distribution $D^A_n$ are a distribution on deterministic programs (the paper does the same in step (ii) of $\pi_{\rm two}$). `outProb μ x b` is $\Pr[A(x)=b]$. If $\iota$ is empty and $T\ge1$ Lean returns the junk value $0$ (the paper has $n\ge1$).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §3.1, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_DetBP

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- `Pr[A(x) = b]` for a randomized branching program `μ` in the random query model on input
`x : {0,1}^ι`: a deterministic program `P ∼ μ` is drawn, the indices `i_1, …, i_T` are i.i.d.
uniform on `ι` and independent of `P`, and `P` is run on the samples `(i_t, x(i_t))`.

**Formalization Note** If `ι` is empty and `T ≥ 1` there is no index sequence and Lean returns
the junk value `0` (`(0 : ℝ)⁻¹ = 0`); the paper has `n ≥ 1`. -/
noncomputable def outProb {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinDist (DetBP W (ι × Bool) T)) (x : ι → Bool) (b : Bool) : ℝ :=
  ∑ P, ∑ i : Fin T → ι, μ.prob P * (Fintype.card (Fin T → ι) : ℝ)⁻¹ *
    (if P.output (fun t => (i t, x (i t))) = b then 1 else 0)

/-- The probability of success `Pr[A(x) = F(x)]` on input `x` of a randomized branching
program `μ` computing `F : {0,1}^ι → {0,1}` in the random query model (Garg, Sundaresan,
Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, §3.1,
pp.13–14 = PDF pp.15–16): "The input is accessed via random samples of the form (i, x(i)) where
i ∈ [n] is chosen … [from] the uniform distribution over [n]"; the randomness is over the
program drawn from `D^A_n`, the sampled edges and the indices.

**Formalization Note** A randomized branching program of width `W` and length `T` is a
probability distribution `μ` on the finite set of deterministic layered programs
`DetBP W (ι × Bool) T`. The per-node edge distributions of §3.1 (iii) fold into `μ`: a run
visits one node per layer, so independent edge choices at the nodes combined with `D^A_n` are a
distribution on deterministic programs (the paper does the same in step (ii) of π_two). The
paper's "final success probability is the minimum success probability over all input x"; a
bound on it is a bound on `successProb μ F x` for every `x`. -/
noncomputable def successProb {W T : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : FinDist (DetBP W (ι × Bool) T)) (F : (ι → Bool) → Bool) (x : ι → Bool) : ℝ :=
  outProb μ x (F x)

end RandomQueryXOR


