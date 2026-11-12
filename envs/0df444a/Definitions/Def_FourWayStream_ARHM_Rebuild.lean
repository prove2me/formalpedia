-- Prove2me | Definitions.Def_FourWayStream_ARHM_Rebuild
-- name    : FourWayStream_ARHM_Rebuild
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:41:55.076199+00:00
-- url     : https://prove2.me/theorems/0ba22e1e-4141-4ecd-a292-a8078319224a
-- title:
--   §4.5, §5.1, §5.1.1 — rebuilt phase states, wrong-parity probability, batches, gaps, banks and good schedules
-- statement:
--   **Rebuilt phase states.** For a batch in which coordinate $j$ receives $\kappa_j$ updates, every register built from it ends in
--   $$|\phi_\kappa(x)\rangle=\frac{1}{\sqrt N}\sum_{j=1}^N e^{i\pi\kappa_j x_j/\mu}|j\rangle .$$
--   Measuring a vector $\varphi$ in the basis $\{(|u\rangle+(-1)^b|v\rangle)/\sqrt2:\{u,v\}\in M,\ b\in\{0,1\}\}$ of a perfect matching $M$ returns $(\{u,v\},b)$ with probability $|\varphi_u+(-1)^b\varphi_v|^2/2$; the **wrong-parity probability** is the total probability of the outcomes with $b=1\oplus x_u\oplus x_v$.
--
--   **Batches.** For an arrival order $\tau$ of the $NL$ labeled updates and a set $B$ of positions, $\kappa_j$ is the number of updates to coordinate $j$ at positions in $B$.
--
--   **Gaps, banks, schedules.** In an arrival order of the whole stream, request $t$ lies in **gap** $j$ if exactly $j$ updates arrive before it, $0\le j\le NL$. With batches of $\mu N$ updates, gaps $0,\dots,\mu N-1$ form the initial interval, gaps $\beta\mu N,\dots,(\beta+1)\mu N-1$ are served by bank $\beta$ ($1\le\beta<\mu$) and gap $NL=\mu^2N$ by bank $\mu$; in all cases the bank is $\lfloor j/(\mu N)\rfloor$. With $P=\lceil 9\log_2(m+1)\rceil$, a schedule is **good** if no request arrives in the initial interval and no bank serves more than $P$ requests. The rising factorial is $a^{\bar k}=a(a+1)\cdots(a+k-1)$, $a^{\bar 0}=1$.
--
--   These objects are used in the analysis of the random-order quantum algorithm (Lemmas 5.4–5.6).
--
--   **Formalization Note** Positions and gaps are 0-based natural numbers; the batch parameter $\mu$ is written `mu`.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §4.5, p.18; §5.1, pp.19–20; §5.1.1, p.21

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false

/-!
# Rebuilt phase states, batches, gaps and schedules (the random-order upper bound)

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): §4.5 (p.18),
§5.1 and §5.1.1 (pp.19–21).

Indices are 0-based: the positions of the `N L` updates in their arrival order are `Fin (N * L)`, the
gaps are `0, …, N L` (gap `j` holds the requests that arrive after exactly `j` updates).
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM

/-- p.20: the state `|ϕ_κ(x)⟩ = N^{−1/2} Σ_j e^{iπ κ_j x_j / µ} |j⟩` built by a batch with counts
`κ`, as its vector of amplitudes. -/
def rebuiltState {N : ℕ} (mu : ℕ) (x : Fin N → Bool) (κ : Fin N → ℕ) : Fin N → ℂ :=
  fun j => ((Real.sqrt N)⁻¹ : ℂ) *
    Complex.exp (Complex.I * (Real.pi * (κ j : ℝ) * (if x j then 1 else 0) / mu : ℝ))

/-- §4.5 (p.18): measuring the vector `φ` in the basis
`{(|u⟩ + (−1)^b |v⟩)/√2 : {u, v} ∈ M, b ∈ {0, 1}}` of the perfect matching `M` returns
`({u, v}, b)` with probability `|φ_u + (−1)^b φ_v|² / 2`. This is the total probability of an outcome
with the wrong parity `b = 1 ⊕ x_u ⊕ x_v` (each edge counted once, as `u < v`). -/
def wrongParityProb {N : ℕ} (M : Finset (Sym2 (Fin N))) (x : Fin N → Bool) (φ : Fin N → ℂ) : ℝ :=
  ∑ u : Fin N, ∑ v : Fin N,
    if u < v ∧ s(u, v) ∈ M then
      ‖φ u + (if !(xor (x u) (x v)) then (-1 : ℂ) else 1) * φ v‖ ^ 2 / 2
    else 0

/-- Lemma 5.4 (p.20): `κ_j`, the number of updates to coordinate `j` at the positions `B` of the
arrival order `τ` of the `N L` labeled updates. -/
def batchCounts {N L : ℕ} (τ : Fin (N * L) ≃ Fin N × Fin L) (B : Finset (Fin (N * L))) :
    Fin N → ℕ :=
  fun j => (B.filter (fun i => (τ i).1 = j)).card

/-- §5.1.1 (p.21): the number of updates that arrive before stream position `i` in the arrival
order `σ`. -/
def updatesBefore {N m L : ℕ} (σ : Arrival N m L) (i : Fin (N * L + m)) : ℕ :=
  (Finset.univ.filter (fun i' => i' < i ∧ (σ i').isLeft)).card

/-- §5.1.1 (p.21): the gap of request `t`: the number of updates that arrive before it (request
`t` lies in gap `j` if it arrives after exactly `j` updates). -/
def requestGap {N m L : ℕ} (σ : Arrival N m L) (t : Fin m) : ℕ :=
  updatesBefore σ (σ.symm (Sum.inr t))

/-- Lemma 5.5 (p.21): the number `Y` of requests in the set `J` of gaps. -/
def requestsIn {N m L : ℕ} (σ : Arrival N m L) (J : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin m => requestGap σ t ∈ J)).card

/-- p.20: the bank size `P = ⌈9 log(m + 1)⌉` (logarithm base 2). -/
def bankSize (m : ℕ) : ℕ := ⌈9 * Real.logb 2 ((m : ℝ) + 1)⌉₊

/-- p.21: the bank serving gap `g` when batches have `µN` updates: gaps `0, …, µN − 1` form the
initial interval (`0`), gaps `βµN, …, (β+1)µN − 1` are served by bank `β` for `1 ≤ β < µ`, and gap
`N L = µ²N` by bank `µ`; all three cases are `⌊g/(µN)⌋`. -/
def bankOf (mu N g : ℕ) : ℕ := g / (mu * N)

/-- p.21: a schedule is good if no request arrives in the initial interval and no bank must serve
more than `P` requests. -/
def IsGoodSchedule {N m L : ℕ} (mu P : ℕ) (σ : Arrival N m L) : Prop :=
  (∀ t, bankOf mu N (requestGap σ t) ≠ 0) ∧
    ∀ β, 1 ≤ β → (Finset.univ.filter (fun t => bankOf mu N (requestGap σ t) = β)).card ≤ P

/-- The rising factorial `a^{k̄} = a (a + 1) ⋯ (a + k − 1)`, `a^{0̄} = 1` (p.21). -/
def risingFact (a : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (a + i)

end FourWayStream.ARHM


