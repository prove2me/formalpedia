-- Prove2me | Definitions.Def_ContagionGrowth_FluidLimit_Network
-- name    : ContagionGrowth_FluidLimit_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:31.001035+00:00
-- url     : https://prove2.me/theorems/4ba9b3a1-5391-4f37-9a1d-952ebd133d6f
-- title:
--   §2.1, (2), (4), (17), pp. 5–8, 21 — directed configuration model and threshold cascade with growth, |D_f|, S_{λ,θ}(k_stop)
-- statement:
--   This file defines the finite random network and the dynamic threshold cascade with growth of Amini, Minca and Sulem.
--
--   **Network.** There are $n$ nodes $[n]=\{1,\dots,n\}$; node $i$ has connectivity $\lambda_i\in\mathbb N$ (in-degree = out-degree $=\lambda_i$) and initial threshold $\theta_i\in\mathbb N$. The empirical type distribution and mean connectivity are
--   $$\mu^{(n)}_{\lambda,\theta}=\frac{\#\{i\in[n]\mid\theta_i=\theta,\ \lambda_i=\lambda\}}{n},\qquad \bar\lambda^{(n)}=\frac1n\sum_{i}\lambda_i=\sum_{\lambda,\theta}\lambda\mu^{(n)}_{\lambda,\theta}.$$
--   Node $i$ owns $\lambda_i$ out-going and $\lambda_i$ in-coming half-edges, $m=n\bar\lambda^{(n)}$ of each kind. In the **directed configuration model** the out-half-edges are matched to the in-half-edges by a uniformly random bijection $\sigma$; the out-half-edge $h$ of node $i$ and the in-half-edge $\sigma(h)$ of node $j$ form a link from $i$ to $j$ (self-loops and multiple links are allowed).
--
--   **Randomness.** Independently of $\sigma$: gaps $\Delta_1,\dots,\Delta_m$ i.i.d. exponential with rate $n$, giving interaction times $T_k=\Delta_1+\dots+\Delta_k$; and $U_1,\dots,U_m$ i.i.d. uniform on $[0,1)$. The probability $P_n$ of a set of outcomes $(\sigma,\Delta,U)$ averages over the $m!$ matchings the product law of $(\Delta,U)$.
--
--   **Cascade.** At time $0$ the nodes with $\theta_i=0$ fail. At the $k$-th interaction, if some failed node has an unrevealed out-half-edge, one of them is revealed, chosen uniformly given the past (the one in position $\lfloor U_k c\rfloor$ among the $c$ available ones, listed node by node); its counterparty $j$ receives one more failed link, and fails if its number $\ell_j$ of failed links satisfies
--   $$\ell_j\ \ge\ \theta_j+\alpha\frac{\lambda_j}{\bar\lambda^{(n)}}T_k,$$
--   its threshold at that time (Remark 2). Failed nodes stay failed and no longer grow. When no failed node has an unrevealed out-half-edge the cascade has stopped; this happens after at most $m$ interactions.
--
--   **Outputs.** $|\mathcal D^{(n)}_f|$ is the number of failed nodes at the end, $k^{(n)}_{\rm stop}$ the number of interactions made, and $S^{(n)}_{\lambda,\theta}(k^{(n)}_{\rm stop})$ the number of surviving nodes with connectivity $\lambda$ and initial threshold $\theta$.
--
--   These are the random quantities whose scaling limits Theorem 5 identifies.
--
--   **Formalization Note.** Half-edges of node $i$ are the pairs $(i,a)$, $a<\lambda_i$; the same type indexes out- and in-half-edges. The matching is uniform on permutations of the half-edges, and $P_n$ is written as an explicit average over permutations (no σ-algebra on permutations is needed). The prose of p. 7 says a node fails when its failed links "exceed" its threshold, while every formula of the paper ($D^{(n)}_{\lambda,\theta}$, $B^\alpha$, $B=\mathbb P(\mathrm{Bin}(\lambda,\pi)\ge\theta)$) uses $\ge$; the formulas are followed. The set $\mathcal D_0$ of initially failed nodes is $\{\theta_i=0\}$, as in the proof's initial condition (p. 21). The cascade is run for exactly $m$ steps (later steps change nothing). If $\bar\lambda^{(n)}=0$ the growth term is $0$ by Lean's convention $x/0=0$; then there are no links at all.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), pp. 5–8 and 21: §2.1, (2), (4), Remark 2, footnote 1, (17)

import Mathlib

namespace ContagionGrowth.FluidLimit

open MeasureTheory ProbabilityTheory

/-- Half-edges of a network on `[n]` with degree sequence `deg`: node `i` owns the `deg i`
half-edges `(i, a)`, `a < deg i`. Since in-degree equals out-degree (p. 5), the same type indexes
the out-half-edges and the in-half-edges. -/
abbrev HalfEdge {n : ℕ} (deg : Fin n → ℕ) : Type := Σ i : Fin n, Fin (deg i)

/-- Number of half-edges of each kind, `m = Σ_i λ_i = n λ̄⁽ⁿ⁾` (p. 7). -/
def numHalfEdges {n : ℕ} (deg : Fin n → ℕ) : ℕ := ∑ i, deg i

/-- Position of the half-edge `(i, a)` when half-edges are listed node by node:
`Σ_{k < i} deg k + a`. -/
def rank {n : ℕ} (deg : Fin n → ℕ) (h : HalfEdge deg) : ℕ :=
  (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < h.1), deg k) + h.2

/-- The half-edge of `s` in position `j` (0-based) when `s` is listed in increasing `rank`. -/
noncomputable def pick {n : ℕ} (deg : Fin n → ℕ) (s : Finset (HalfEdge deg)) (j : ℕ) :
    Option (HalfEdge deg) := by
  classical
  exact if h : ∃ x ∈ s, (s.filter fun y => rank deg y < rank deg x).card = j then some h.choose
    else none

/-- Empirical type fraction `µ⁽ⁿ⁾_{λ,θ} = #{i ∈ [n] | θ_i = θ, λ_i = λ}/n`, (2), p. 6. -/
noncomputable def muN {n : ℕ} (deg θs : Fin n → ℕ) (lam θ : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => θs i = θ ∧ deg i = lam).card : ℝ) / n

/-- Average connectivity `λ̄⁽ⁿ⁾ = Σ_{λ,θ} λ µ⁽ⁿ⁾_{λ,θ} = (Σ_i λ_i)/n`, (4), p. 6. -/
noncomputable def lbarN {n : ℕ} (deg : Fin n → ℕ) : ℝ := (∑ i, (deg i : ℝ)) / n

/-- State of the cascade after some interactions: the failed nodes, the number of failed
(revealed) in-coming links of each node, and the set of revealed out-half-edges. -/
structure CascadeState {n : ℕ} (deg : Fin n → ℕ) where
  failed : Finset (Fin n)
  failedLinks : Fin n → ℕ
  revealed : Finset (HalfEdge deg)

/-- Initial state: `D₀ = {i | θ_i = 0}` has failed, nothing is revealed. -/
def initState {n : ℕ} (deg θs : Fin n → ℕ) : CascadeState deg :=
  ⟨Finset.univ.filter (fun i => θs i = 0), fun _ => 0, ∅⟩

/-- One outcome of the randomness of a network of size `n`: the configuration-model matching
`σ` (out-half-edge `h` is matched to in-half-edge `σ h`, so the link goes from node `h.1` to node
`(σ h).1`), the inter-interaction gaps `Δ_1, …, Δ_m` (stored at indices `0, …, m-1`), and the
uniform variables `U_1, …, U_m` that choose the link revealed at each interaction. -/
abbrev Outcome {n : ℕ} (deg : Fin n → ℕ) : Type :=
  Equiv.Perm (HalfEdge deg) × (Fin (numHalfEdges deg) → ℝ) × (Fin (numHalfEdges deg) → ℝ)

/-- Calendar time of the `k`-th interaction, `T_k = Δ_1 + ⋯ + Δ_k`. -/
def interactionTime {m : ℕ} (Δ : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < k), Δ i

/-- One interaction of the cascade (p. 7). If no failed node has an unrevealed out-half-edge, the
state is unchanged (the cascade has stopped). Otherwise this is interaction number `k + 1`, where
`k` is the number of links revealed so far: the unrevealed out-half-edges of failed nodes are
listed in increasing `rank`, and the one in position `⌊U_{k+1} c⌋` (`c` = their number) is
revealed — uniform among them given the past (footnote 1). Its counterparty `j` gets one more
failed link, and fails if its number of failed links reaches its current threshold
`θ_j + α λ_j T_{k+1}/λ̄⁽ⁿ⁾` (Remark 2). -/
noncomputable def step {n : ℕ} (deg θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg)
    (s : CascadeState deg) : CascadeState deg :=
  let avail := Finset.univ.filter (fun h : HalfEdge deg => h.1 ∈ s.failed ∧ h ∉ s.revealed)
  let k := s.revealed.card
  let u : ℝ := if hk : k < numHalfEdges deg then ω.2.2 ⟨k, hk⟩ else 0
  match pick deg avail (min ⌊u * avail.card⌋₊ (avail.card - 1)) with
  | none => s
  | some h =>
    let j := (ω.1 h).1
    let T := interactionTime ω.2.1 (k + 1)
    let lj := s.failedLinks j + 1
    { failed := if (θs j : ℝ) + α * deg j * T / lbarN deg ≤ (lj : ℝ) then insert j s.failed
        else s.failed
      failedLinks := Function.update s.failedLinks j lj
      revealed := insert h s.revealed }

/-- State at the end of the cascade: `m = n λ̄⁽ⁿ⁾` interactions suffice ("it stops at most after
`n λ̄⁽ⁿ⁾` interactions", p. 7), after which `step` leaves the state unchanged. -/
noncomputable def finalState {n : ℕ} (deg θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg) :
    CascadeState deg :=
  (step deg θs α ω)^[numHalfEdges deg] (initState deg θs)

/-- `|D_f⁽ⁿ⁾|`, the number of failed nodes at the end of the cascade. -/
noncomputable def numFailed {n : ℕ} (deg θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg) : ℕ :=
  (finalState deg θs α ω).failed.card

/-- `k_stop⁽ⁿ⁾`, the number of interactions of the cascade (17). -/
noncomputable def kStop {n : ℕ} (deg θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg) : ℕ :=
  (finalState deg θs α ω).revealed.card

/-- `S⁽ⁿ⁾_{λ,θ}(k_stop)`, the number of nodes of degree `λ` and initial threshold `θ` that survive
the cascade. -/
noncomputable def survivors {n : ℕ} (deg θs : Fin n → ℕ) (α : ℝ) (lam θ : ℕ) (ω : Outcome deg) :
    ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    deg i = lam ∧ θs i = θ ∧ i ∉ (finalState deg θs α ω).failed).card

/-- Law of the gaps: `Δ_1, …, Δ_m` i.i.d. `Exp(n)` (rate `n`, mean `1/n`), p. 7. -/
noncomputable def gapsLaw {n : ℕ} (deg : Fin n → ℕ) : Measure (Fin (numHalfEdges deg) → ℝ) :=
  Measure.pi fun _ => expMeasure (n : ℝ)

/-- Law of the revelation choices: `U_1, …, U_m` i.i.d. uniform on `[0, 1)`. -/
noncomputable def choiceLaw {n : ℕ} (deg : Fin n → ℕ) : Measure (Fin (numHalfEdges deg) → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Ico (0 : ℝ) 1)

/-- Probability `P_n(E)` of a set of outcomes of the network of size `n`: the matching `σ` is
uniform on the `m!` permutations, independent of the gaps and the choices. -/
noncomputable def netProb {n : ℕ} (deg : Fin n → ℕ) (E : Set (Outcome deg)) : ENNReal := by
  classical
  exact ∑ σ : Equiv.Perm (HalfEdge deg),
    ((Fintype.card (Equiv.Perm (HalfEdge deg)) : ENNReal))⁻¹ *
      ((gapsLaw deg).prod (choiceLaw deg)) {x | (σ, x) ∈ E}

end ContagionGrowth.FluidLimit


