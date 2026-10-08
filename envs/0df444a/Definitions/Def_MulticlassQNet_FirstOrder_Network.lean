-- Prove2me | Definitions.Def_MulticlassQNet_FirstOrder_Network
-- name    : MulticlassQNet_FirstOrder_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:49:18.537003+00:00
-- url     : https://prove2.me/theorems/3554e3c5-6052-4d06-9402-48d87893eff6
-- title:
--   §2 — open multiclass network data: stations σ, routing p_rs, arrival rates λ_0r, service rates μ_r; traffic equations (15), openness, load
-- statement:
--   An **open multiclass queueing network** has $N$ single-server stations and $R$ job classes. Each class $r$ is served at the station $\sigma(r)$; $C_i=\{r:\sigma(r)=i\}$ is the set of classes served at station $i$. When a class-$r$ job completes service it becomes a class-$s$ job with probability $p_{rs}\ge 0$, or leaves the network with probability
--   $$p_{r0}=1-\sum_{s=1}^R p_{rs}\ \ge 0 .$$
--   Class-$r$ jobs arrive from outside as an independent Poisson stream of rate $\lambda_{0r}\ge 0$, and class-$r$ service times are exponential with rate $\mu_r>0$.
--
--   Three notions attached to this data are defined alongside it.
--
--   1. A vector $(\lambda_r)_r$ solves the **traffic equations** (15) if
--   $$\lambda_r=\lambda_{0r}+\sum_{r'=1}^R\lambda_{r'}p_{r'r},\qquad r=1,\dots,R.$$
--   2. The network is **open** if the homogeneous system $v_r=\sum_{r'}v_{r'}p_{r'r}$ has only the solution $v=0$, so that (15) has exactly one solution.
--   3. The **load condition** of §4.1 holds for $\lambda$ if $\sum_{r\in C_i}\lambda_r/\mu_r<1$ at every station $i$.
--
--   These are the standing data of every result in Sections 2 and 4 of the paper.
--
--   **Formalization Note** Classes are `Fin R` and stations `Fin N`; the paper's class $r$ is `r.val + 1`, and the exit "class 0" is not a class but the quantity `exitProb r`. The external rates are named `lam0` because `λ` is a Lean keyword. Openness is not written on the page as a formula; the paper calls the network open and speaks of "the solution" of (15) (p. 19), which this condition encodes.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 6, §2 (network model); p. 13, §4.1, Eq. (15) and the load condition

import Mathlib

namespace MulticlassQNet.FirstOrder

/-- Open multiclass queueing network data (Bertsimas–Paschalidis–Tsitsiklis 1992, §2, p. 6):
`N` single-server stations and `R` job classes. Class `r` is served at station `σ r`; after
service a class-`r` job becomes a class-`s` job with probability `p r s`, or exits with
probability `1 - ∑ s, p r s`; class-`r` jobs arrive from outside as a Poisson stream of rate
`lam0 r`; class-`r` service times are exponential with rate `μ r`. -/
structure Network (N R : ℕ) where
  /-- station of each class, the paper's `σ(r)` -/
  σ : Fin R → Fin N
  /-- routing probabilities `p_{rs}` -/
  p : Fin R → Fin R → ℝ
  /-- external arrival rates `λ_{0r}` -/
  lam0 : Fin R → ℝ
  /-- service rates `μ_r` -/
  μ : Fin R → ℝ
  p_nonneg : ∀ r s, 0 ≤ p r s
  p_row_sum_le_one : ∀ r, ∑ s, p r s ≤ 1
  lam0_nonneg : ∀ r, 0 ≤ lam0 r
  μ_pos : ∀ r, 0 < μ r

namespace Network

variable {N R : ℕ} (net : Network N R)

/-- The exit probability `p_{r0} = 1 - ∑_s p_{rs}`. -/
def exitProb (r : Fin R) : ℝ := 1 - ∑ s, net.p r s

/-- `C_i`, the set of classes served at station `i`. -/
def C (i : Fin N) : Finset (Fin R) := Finset.univ.filter (fun r => net.σ r = i)

/-- `lam` solves the traffic equations (15):
`λ_r = λ_{0r} + ∑_{r'} λ_{r'} p_{r'r}` for every class `r`. -/
def IsTrafficSolution (lam : Fin R → ℝ) : Prop :=
  ∀ r, lam r = net.lam0 r + ∑ r', lam r' * net.p r' r

/-- The network is open: the homogeneous traffic system `v_r = ∑_{r'} v_{r'} p_{r'r}` has only
the zero solution (equivalently `I - Pᵀ` is invertible), so (15) has a unique solution. -/
def IsOpen : Prop :=
  ∀ v : Fin R → ℝ, (∀ r, v r = ∑ r', v r' * net.p r' r) → v = 0

/-- The load condition of §4.1 (p. 13): `∑_{r ∈ C_i} λ_r / μ_r < 1` at every station `i`. -/
def LoadLtOne (lam : Fin R → ℝ) : Prop :=
  ∀ i, ∑ r ∈ net.C i, lam r / net.μ r < 1

end Network

end MulticlassQNet.FirstOrder


