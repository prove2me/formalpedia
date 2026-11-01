-- Prove2me | Definitions.Def_AssignToSeatRM_Dynamic
-- name    : AssignToSeatRM_Dynamic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:50.665978+00:00
-- url     : https://prove2.me/theorems/64675438-8d1e-4141-8791-cf403635547c
-- title:
--   The dynamic problem: instances, the $\theta$-th problem, policies, $V^\pi_\theta$, $V^{HO}_\theta$, RDP-consistency, NEE and $\lambda_{\min}$
-- statement:
--   **Instance** $I=\langle C,\{p_{ij}\},\{\lambda^t_{ij}\}\rangle$: a capacity matrix $C\in\{0,1\}^{N\times M}$, prices $p_{ij}\ge0$, and arrival probabilities $\lambda^t_{ij}\ge0$ for periods $t\in[T]$ with $\sum_{i\le j}\lambda^t_{ij}\le1$; with probability $\lambda^t_0=1-\sum_{i\le j}\lambda^t_{ij}$ no request arrives in period $t$. Arrivals are independent across periods.
--
--   **The $\theta$-th problem** ($\theta\ge1$): $C(\theta)\in\{0,1\}^{\theta N\times M}$ stacks $\theta$ copies of $C$, $C(\theta)_{(k+(s-1)N)\ell}=C_{k\ell}$, the horizon is $\theta T$ and $\lambda^t_{ij}(\theta)=\lambda^{\lceil t/\theta\rceil}_{ij}$.
--
--   **Policies.** A policy chooses, in each period, after seeing the request $i\to j$, a seat that is free on legs $i,\dots,j$, or rejects; the assignment is final, rejected requests are lost. $V^\pi_\theta(I)$ is the expected revenue of $\pi$ in the $\theta$-th problem.
--
--   **Hindsight optimum.** $V^{HO}_\theta(I)=\mathbb E\big[\text{value of LP (2) for } C(\theta) \text{ and the realized demand } d^{[1,\theta T]}\big]$.
--
--   **RDP** (Algorithm 3). In period $t$, after observing $i^t\to j^t$, RDP solves (14) with $A=f(C^t)$ and $d=\lambda^{[t,\theta T]}=\sum_{t'=t}^{\theta T}\lambda^{t'}(\theta)$ together with (15), takes an optimal solution $\gamma$, picks an option $(u^t,v^t)$ maximizing $\gamma_{u i^tj^tv}$ (rejection $[0,0]$ included, ties broken arbitrarily), and puts the request on a seat of $M_{u^tv^t}(C^t)$ (or rejects). A policy is **RDP-consistent** if at every history of positive probability its decision is one RDP can make.
--
--   **NEE** (Definition 3): every itinerary with $\lambda^{[1,T]}_{ij}>0$ has $\lambda^T_{ij}>0$. Finally $T_{ij}=\sup\{t\le T:\lambda^t_{ij}>0\}$ and $\lambda_{\min}=\min_{i\le j}\lambda^{T_{ij}}_{ij}/T_{ij}$ over the itineraries that can arrive.
--
--   **Formalization Note** A request sequence is $\omega:\mathrm{Fin}(H)\to\mathrm{Option}(\text{itinerary})$, its probability the product of the per-period probabilities, and an expectation the finite sum over sequences. A policy is deterministic and non-anticipating (its decision in period $s+1$ depends only on the requests of periods $1,\dots,s+1$); naming a seat that is not free counts as a rejection. Seat $m$ (0-based) of $C(\theta)$ copies seat $m \bmod N$ of $C$; $\lceil t/\theta\rceil$ is $(t+\theta-1)/\theta$ in $\mathbb N$. $\lambda_{\min}$ is $1$ when no itinerary can arrive.
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, §2 pp.8–9 (model), §4 pp.13–14 (instance, θ-scaling, V^π, HO), Algorithm 3 p.20, Definition 3 p.20, proof of Theorem 4 pp.ec21–ec22 (T_ij, λ_min)

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_StaticLP
import Definitions.Def_AssignToSeatRM_DynamicPrimal

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-! # The dynamic problem: instances, the θ-th problem, policies, HO, RDP and NEE

Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023, doi:10.1287/msom.2023.1188, §2 (pp.8–9),
§4 (pp.13–14), Algorithm 3 (p.20), Definition 3 (p.20); `λ_min` and `T_{ij}` from the proof of
Theorem 4 (pp.ec21–ec22).

**Formalization Note.**
1. *Instance* `I = ⟨C, {p_{ij}}, {λ^t_{ij}}⟩` (p.13): `C : CapMat N M`, prices
   `p : ℕ → ℕ → ℝ` with `p_{ij} ≥ 0` (`IsPriceVec`; fares, p.8), arrival probabilities
   `lam : ℕ → ℕ → ℕ → ℝ`, `lam t i j = λ^t_{ij}` for the 1-based period `t`, with
   `λ^t_{ij} ≥ 0` and `Σ_{i ≤ j} λ^t_{ij} ≤ 1` for `t ∈ [T]` (`IsArrivalProb`, p.8).
2. *θ-th problem* (p.13), `θ ≥ 1`: `capScale C θ : CapMat (θN) M` gives seat `m` (0-based) the
   row of seat `m mod N`, i.e. the paper's `C(θ)_{(k+(s−1)N)ℓ} = C_{kℓ}`; the horizon is `θT`
   and `lamScale lam θ t = λ^{⌈t/θ⌉}` (`⌈t/θ⌉ = (t + θ − 1)/θ` in `ℕ`).
3. *Randomness.* A request sequence of horizon `H` is `ω : Fin H → Option (Itin M)`; `ω s` is
   the request of the 1-based period `s + 1` (`none`: no arrival, probability `λ^t_0`). Its
   probability is the product `Π_t q_t(ω_t)` (arrivals independent across periods), and the
   expectation is the finite sum `Σ_ω P(ω) X(ω)`.
4. *Policies* (p.8) are deterministic and non-anticipating: in period `s + 1` the decision
   (a seat `k`, or reject = `none`) may depend on the requests of periods `1, …, s + 1`. An
   accepted request `i → j` must go to a seat free on legs `i, …, j`; a decision naming a seat
   that is not free is a rejection. Rejected requests are lost (p.9).
5. *HO* (p.14): the expectation of the optimal value of LP (2) for `C(θ)` and the realized
   demand `d^{[1,θT]}`.
6. *RDP* (Algorithm 3, p.20): `IsRDP` states that a policy makes, at every history of positive
   probability, a decision RDP can make; it is stated for every optimal solution and every
   tie-break (the Lean goal quantifies over all such policies). -/

/-- Prices are nonnegative, `p_{ij} ≥ 0` for `i ≤ j` (fares, p.8). -/
def IsPriceVec (M : ℕ) (p : ℕ → ℕ → ℝ) : Prop :=
  ∀ ij ∈ itins M, 0 ≤ p ij.1 ij.2

/-- Arrival probabilities (p.8): `λ^t_{ij} ≥ 0` and `Σ_{1 ≤ i ≤ j ≤ M} λ^t_{ij} ≤ 1` for every
period `t ∈ [T]`. -/
def IsArrivalProb (M T : ℕ) (lam : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, (∀ ij ∈ itins M, 0 ≤ lam t ij.1 ij.2) ∧
    ∑ ij ∈ itins M, lam t ij.1 ij.2 ≤ 1

/-- The arrival probabilities of the θ-th problem (p.13): `λ^t_{ij}(θ) = λ^{⌈t/θ⌉}_{ij}` for the
1-based period `t ∈ [θT]` (`⌈t/θ⌉ = (t + θ − 1)/θ` for `θ ≥ 1`). -/
def lamScale (lam : ℕ → ℕ → ℕ → ℝ) (θ : ℕ) : ℕ → ℕ → ℕ → ℝ :=
  fun t i j => lam ((t + θ - 1) / θ) i j

theorem mod_lt_of_lt_mul {m θ N : ℕ} (h : m < θ * N) : m % N < N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp at h
  · exact Nat.mod_lt _ hN

/-- The capacity matrix of the θ-th problem (p.13): `θ` stacked copies of `C`; seat `m`
(0-based) of `C(θ)` is a copy of seat `m mod N` of `C`. -/
def capScale {N M : ℕ} (C : CapMat N M) (θ : ℕ) : CapMat (θ * N) M :=
  fun m ℓ => C ⟨m.val % N, mod_lt_of_lt_mul m.isLt⟩ ℓ

/-- Request sequences of horizon `H`: `ω s` is the request of period `s + 1`, or `none`. -/
abbrev ReqSeq (H M : ℕ) := Fin H → Option (Itin M)

/-- The probability of the request `r` in the 1-based period `t` under arrival probabilities
`q`: `q^t_{ij}` for `r = i → j`, and `λ^t_0 = 1 − Σ_{i ≤ j} q^t_{ij}` for no arrival (p.8). -/
def periodProb (M : ℕ) (q : ℕ → ℕ → ℕ → ℝ) (t : ℕ) : Option (Itin M) → ℝ
  | none => 1 - ∑ ij ∈ itins M, q t ij.1 ij.2
  | some ij => q t ij.1.1 ij.1.2

/-- The probability of a request sequence: arrivals are independent across periods. -/
def seqProb (M H : ℕ) (q : ℕ → ℕ → ℕ → ℝ) (ω : ReqSeq H M) : ℝ :=
  ∏ s : Fin H, periodProb M q (s.val + 1) (ω s)

/-- The expectation of `X` over request sequences of horizon `H`. -/
def expect (M H : ℕ) (q : ℕ → ℕ → ℕ → ℝ) (X : ReqSeq H M → ℝ) : ℝ :=
  ∑ ω : ReqSeq H M, seqProb M H q ω * X ω

/-- The realized demand `d^{[1,H]}_{ij}`: the number of periods with a request `i → j`. -/
def realizedDemand {H M : ℕ} (ω : ReqSeq H M) (i j : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin H => (ω s).map Subtype.val = some (i, j))).card

/-- The expected demand `λ^{[t,H]}_{ij} = Σ_{t'=t}^{H} q^{t'}_{ij}` of periods `t, …, H`. -/
def remainingMean (q : ℕ → ℕ → ℕ → ℝ) (t H i j : ℕ) : ℝ :=
  ∑ t' ∈ Finset.Icc t H, q t' i j

/-- A deterministic, non-anticipating policy (p.8) for horizon `H`, `M` legs and `K` seats:
`act s ω` is the seat assigned to the request of period `s + 1` (or `none`: reject), and it
depends only on the requests of periods `1, …, s + 1`. -/
structure Policy (H M K : ℕ) where
  act : Fin H → ReqSeq H M → Option (Fin K)
  nonanticipating : ∀ (s : Fin H) (ω ω' : ReqSeq H M),
    (∀ r : Fin H, r ≤ s → ω r = ω' r) → act s ω = act s ω'

/-- The capacity matrix after one period with request `req` and decision `dec`: the request is
accepted iff it is a request `i → j` and the chosen seat is free on legs `i, …, j`. -/
def stepCap {K M : ℕ} (C : CapMat K M) : Option (Itin M) → Option (Fin K) → CapMat K M
  | some ij, some k => if IsFreeOn C k ij.1.1 ij.1.2 then assignSeat C k ij.1.1 ij.1.2 else C
  | _, _ => C

/-- The revenue of one period: `p_{ij}` if the request `i → j` is accepted, else `0`. -/
def stepRevenue {K M : ℕ} (p : ℕ → ℕ → ℝ) (C : CapMat K M) :
    Option (Itin M) → Option (Fin K) → ℝ
  | some ij, some k => if IsFreeOn C k ij.1.1 ij.1.2 then p ij.1.1 ij.1.2 else 0
  | _, _ => 0

/-- The capacity matrix `C^{s+1}` at the beginning of the 1-based period `s + 1` when `π` is
run on `ω` from `C¹ = C₀`. -/
def runState {H M K : ℕ} (C₀ : CapMat K M) (π : Policy H M K) (ω : ReqSeq H M) :
    ℕ → CapMat K M
  | 0 => C₀
  | s + 1 =>
    if h : s < H then stepCap (runState C₀ π ω s) (ω ⟨s, h⟩) (π.act ⟨s, h⟩ ω)
    else runState C₀ π ω s

/-- The total revenue collected by `π` on `ω`. -/
def policyRevenue {H M K : ℕ} (p : ℕ → ℕ → ℝ) (C₀ : CapMat K M) (π : Policy H M K)
    (ω : ReqSeq H M) : ℝ :=
  ∑ s : Fin H, stepRevenue p (runState C₀ π ω s.val) (ω s) (π.act s ω)

/-- `V^π_θ(I)` (p.13): the expected revenue of `π` in the θ-th problem. -/
def Vpol {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (lam : ℕ → ℕ → ℕ → ℝ) (θ T : ℕ)
    (π : Policy (θ * T) M (θ * N)) : ℝ :=
  expect M (θ * T) (lamScale lam θ) (policyRevenue p (capScale C θ) π)

/-- `V^HO_θ(I)` (p.14): the expectation over sample paths of the optimal value of the static
LP (2) for `C(θ)` and the realized demand `d^{[1,θT]}`. -/
def VHO {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (lam : ℕ → ℕ → ℕ → ℝ) (θ T : ℕ) : ℝ :=
  expect M (θ * T) (lamScale lam θ)
    (fun ω => lp2Value (capScale C θ) p (fun i j => (realizedDemand ω i j : ℝ)))

/-- `π` is a policy that RDP (Algorithm 3, p.20) can produce in the θ-th problem: at every
period `t = s + 1` and every request sequence `ω` of positive probability with request
`ω_t = i → j`, writing `Cᵗ` for the state `π` reaches, there are an optimal solution `γ` of (14)
together with (15) for `A = f(Cᵗ)`, `d = λ^{[t,θT]}` and the request `i → j`, and an option `o`
maximizing `γ_{u i j v}` over `[0,0]` (reject) and the pairs `u ≤ i ≤ j ≤ v`, such that `π`
rejects if `o` is the rejection and assigns a seat `k ∈ M_{uv}(Cᵗ)` if `o = (u, v)`. -/
def IsRDP {N M : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (lam : ℕ → ℕ → ℕ → ℝ) (θ T : ℕ)
    (π : Policy (θ * T) M (θ * N)) : Prop :=
  ∀ (s : Fin (θ * T)) (ω : ReqSeq (θ * T) M) (ij : Itin M),
    0 < seqProb M (θ * T) (lamScale lam θ) ω → ω s = some ij →
      ∃ γ : Idx4 → ℝ,
        IsOptimal1415 M p (fun u v => (fC (runState (capScale C θ) π ω s.val) u v : ℝ))
          (fun i j => remainingMean (lamScale lam θ) (s.val + 1) (θ * T) i j)
          ij.1.1 ij.1.2 γ ∧
        ∃ o : Option (ℕ × ℕ), IsMaxOption M γ ij.1.1 ij.1.2 o ∧
          (o = none → π.act s ω = none) ∧
          (∀ uv : ℕ × ℕ, o = some uv →
            ∃ k ∈ maxSeqSeats (runState (capScale C θ) π ω s.val) uv.1 uv.2,
              π.act s ω = some k)

/-- Definition 3 (NEE, p.20): `inf_{i ≤ j: λ^{[1,T]}_{ij} > 0} λ^T_{ij} > 0`. The index set is
finite, so this is: every itinerary with `λ^{[1,T]}_{ij} > 0` has `λ^T_{ij} > 0`. -/
def IsNEE (M T : ℕ) (lam : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ ij ∈ itins M, 0 < ∑ t ∈ Finset.Icc 1 T, lam t ij.1 ij.2 → 0 < lam T ij.1 ij.2

/-- The itineraries that can arrive: `λ^{[1,T]}_{ij} > 0`. -/
def arrivingTypes (M T : ℕ) (lam : ℕ → ℕ → ℕ → ℝ) : Finset (ℕ × ℕ) :=
  (itins M).filter (fun ij => 0 < ∑ t ∈ Finset.Icc 1 T, lam t ij.1 ij.2)

/-- `T_{ij} = sup{t ≤ T : λ^t_{ij} > 0}` (p.ec21), the last period in which `i → j` can arrive
(`0` if there is none; used only for arriving types). -/
def lastArrival (T : ℕ) (lam : ℕ → ℕ → ℕ → ℝ) (i j : ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter (fun t => 0 < lam t i j)).sup id

/-- `λ_min = inf_{i ≤ j} λ^{T_{ij}}_{ij} / T_{ij}` (p.ec22), the infimum taken over the
itineraries that can arrive (the proof assumes `T_{ij} ≥ 1` "without loss of generality",
p.ec21); `1` when no itinerary can arrive. -/
def lamMin (M T : ℕ) (lam : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  if h : (arrivingTypes M T lam).Nonempty then
    (arrivingTypes M T lam).inf' h
      (fun ij => lam (lastArrival T lam ij.1 ij.2) ij.1 ij.2 /
        (lastArrival T lam ij.1 ij.2 : ℝ))
  else 1

end AssignToSeatRM


