-- Prove2me | Definitions.Def_ErasureQTanner_noisyProb
-- name    : ErasureQTanner_noisyProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:39.328756+00:00
-- url     : https://prove2.me/theorems/7d63d0fa-5279-4e4b-9b02-fabcf605a5c0
-- title:
--   The $\rho$-noisy erasure pattern: $E_{x\sim\rho}$ and $\Pr_{x\sim\rho}$
-- statement:
--   For a finite coordinate set $\iota$ and $\rho\in[0,1]$, a **$\rho$-noisy pattern** $x\sim\rho$ is a random vector $x\in\{0,1\}^\iota$ whose coordinates are independent and equal to $1$ with probability $\rho$. Its law is
--   $$\Pr[x]=\prod_{i\in\iota}\begin{cases}\rho & x_i=1\\ 1-\rho & x_i=0,\end{cases}$$
--   and expectations and probabilities are the corresponding finite sums. A coordinate with $x_i=1$ is **erased**. This is the channel of every result in the mission.
--
--   **Formalization Note** A pattern is a function to `Bool`. The product is a formula defined at every real $\rho$, and it is a probability law exactly for $\rho\in[0,1]$.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §6, p.13

import Mathlib

set_option autoImplicit false

namespace ErasureQTanner

/-- The probability of the pattern `x` under `x ∼ ρ`: Pfister, Sprumont, Zémor, *Classical Tensor Codes and
Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), §6,
p.13: "a random vector `x ∈ F₂ⁿ` whose `i`th coordinate is (independently across coordinates): `xᵢ = 1` with
probability `ρ`, `0` otherwise."

**Formalization Note.** The pattern is a function `x : ι → Bool`, `true` meaning `xᵢ = 1` (erased). The weight is a
formula, so it is defined at every real `ρ`; it is a probability weight exactly for `ρ ∈ [0, 1]`. -/
noncomputable def noisyWeight {ι : Type*} [Fintype ι] (ρ : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i then ρ else 1 - ρ

/-- `E_{x∼ρ}[f(x)]`, a finite sum (§6, p.13). -/
noncomputable def noisyExp {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ x, noisyWeight ρ x * f x

open Classical in
/-- `Pr_{x∼ρ}[E(x)]`, a finite sum (§6, p.13). -/
noncomputable def noisyProb {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ℝ) (E : (ι → Bool) → Prop) : ℝ :=
  noisyExp ρ fun x => if E x then 1 else 0

end ErasureQTanner


