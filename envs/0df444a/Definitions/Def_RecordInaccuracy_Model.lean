-- Prove2me | Definitions.Def_RecordInaccuracy_Model
-- name    : RecordInaccuracy_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:03.280206+00:00
-- url     : https://prove2.me/theorems/8e332148-ff98-416d-a507-821d049ab84e
-- title:
--   Inventory record inaccuracy model: parameters, belief flow (1), Bayes jump (2), shelf inventory distributions
-- statement:
--   A retailer keeps one product on a shelf of capacity $q_m$ and observes only the inventory *record*, never the shelf. The model of §2 has the parameters
--
--   1. demand rate $\lambda_D>0$, transaction-error probability $\alpha\in[0,1]$, unobservable-loss rate $\lambda_L\ge 0$, phantom-sale rate $\lambda_P\ge 0$, discount rate $\rho>0$;
--   2. goodwill cost $c_D>0$, margin $m>0$, purchase cost $c$, loss cost $c_L\ge c$, price difference $\Delta p$, fixed restocking cost $k_R$,
--
--   and the derived rates $\lambda_E=\alpha\lambda_D$, $\lambda_{\hat D}=(1-\alpha)\lambda_D$ and $\lambda_{\hat L}=\lambda_L+\lambda_E$.
--
--   A belief is a probability vector $\Pi=(\Pi_0,\dots,\Pi_{q_m})$ over the shelf stock $q$ ($q=0$ is an empty shelf).
--
--   **Belief flow (1).** Between observable events the belief evolves by
--   $$\dot\Pi_q=\lambda_{\hat L}\Pi_{q+1}\mathbb 1_{\{q<q_m\}}-\lambda_{\hat L}\Pi_q\mathbb 1_{\{q>0\}}+\lambda_{\hat D}\Pi_0\mathbb 1_{\{q=0\}}-\lambda_{\hat D}\Pi_0\Pi_q .$$
--   Its solution from $\Pi(0)=F$ is $\Pi^F(s)=\psi^F(s)/\sum_q\psi^F_q(s)$, where $\psi^F(s)=e^{sM}F$ and $M$ is the generator
--   $$(M\psi)_q=\lambda_{\hat L}\psi_{q+1}\mathbb 1_{\{q<q_m\}}-(\lambda_{\hat L}+\lambda_{\hat D})\psi_q\mathbb 1_{\{q>0\}} .$$
--   Here $\psi^F_q(s)$ is the probability that the stock is $q$ at time $s$ and no correctly recorded sale has occurred.
--
--   **Observable events.** Observable events (a correctly recorded sale while in stock, or a phantom sale) occur at rate $h(\Pi)=\lambda_{\hat D}(1-\Pi_0)+\lambda_P$. Started from $F$, the next one, $\iota$, has survival function $S^F(s)=e^{-\lambda_P s}\sum_q\psi^F_q(s)$.
--
--   **Bayes jump (2).** At an observable event the belief jumps from $\Pi=\Pi(\iota^-)$ to
--   $$J(\Pi)_q=\frac{\lambda_{\hat D}\Pi_{q+1}\mathbb 1_{\{q<q_m\}}+\lambda_P\Pi_q}{\lambda_{\hat D}(1-\Pi_0)+\lambda_P}.$$
--
--   **Shelf inventory distributions.** These are the beliefs reachable from the post-restock belief $\mathbb 1_{\{q=q_m\}}$ by the flow (for any elapsed time $s\ge 0$) and by the jump (at beliefs where $h>0$). For a starting belief $G$, gaps $d_1,\dots,d_k\ge 0$ between events and elapsed time $t$, the belief after that history is $\Pi^{J(\Pi^{\cdots J(\Pi^G(d_1))\cdots}(d_k))}(t)$.
--
--   These objects turn the partially observed control problem into a fully observed problem with piecewise deterministic dynamics. Every theorem of the mission is stated about them.
--
--   **Formalization Note** States are `Fin (q_m+1)`, with index $q$ equal to the stock level (the paper lists $\Pi$ from $\Pi_{q_m}$ down to $\Pi_0$). The flow (1) is written in its closed linear form `NormedSpace.exp (s • M)` followed by normalization. The standing parameter assumptions are the predicate `Standing`. Where $h(\Pi)=0$, the jump is Lean's $0/0=0$ vector; every use excludes it or multiplies it by $h=0$.
-- source:
--   Chehrazi, Inventory Systems with Record Inaccuracy, MSOM (2025), doi:10.1287/msom.2023.0274, §2 pp.8–9 (parameters), eq. (1) p.12, eq. (2) p.13, problem (4) p.16 (law of ι), proof of Theorem 1 p.35 (shelf inventory distributions)

import Mathlib

namespace RecordInaccuracy

/-- **Model parameters** of Chehrazi, *Inventory Systems with Record Inaccuracy: Transaction Errors
vs. Unobservable Loss*, MSOM (2025), doi:10.1287/msom.2023.0274, §2, pp.8–9, and Appendix B,
pp.47–48.

* `qm` — shelf capacity `q_m`;
* `lamD` — demand rate `λ_D`; `alpha` — transaction-error probability `α`;
* `lamL` — unobservable-loss rate `λ_L`; `lamP` — phantom-sale rate `λ_P`;
* `rho` — discount rate `ρ`;
* `cD` — goodwill cost `c_D`; `m` — margin `m = p − c`; `c` — purchase cost; `cL` — loss cost
  `c_L`; `dp` — price difference `Δp = p − p'`; `kR` — fixed restocking cost `k_R`.

The assumptions the paper places on them are the separate predicate `Params.Standing`. -/
structure Params where
  /-- shelf capacity `q_m` -/
  qm : ℕ
  /-- demand rate `λ_D` -/
  lamD : ℝ
  /-- transaction-error probability `α` -/
  alpha : ℝ
  /-- unobservable-loss rate `λ_L` -/
  lamL : ℝ
  /-- phantom-sale rate `λ_P` -/
  lamP : ℝ
  /-- discount rate `ρ` -/
  rho : ℝ
  /-- goodwill cost `c_D` -/
  cD : ℝ
  /-- lost-sale margin `m = p − c` -/
  m : ℝ
  /-- purchase cost `c` -/
  c : ℝ
  /-- loss cost `c_L` -/
  cL : ℝ
  /-- price difference `Δp = p − p'` -/
  dp : ℝ
  /-- fixed restocking cost `k_R` -/
  kR : ℝ

namespace Params

variable (P : Params)

/-- **Standing assumptions** on the parameters (§2, pp.8–9): demand, loss and phantom sales are
Poisson processes with intensities `λ_D > 0`, `λ_L ≥ 0`, `λ_P ≥ 0`; `α ∈ [0, 1]` is a
probability; `ρ > 0` (p.11); `c_D > 0`, `m > 0` and `c_L ≥ c` (p.9). No sign is imposed on `c`,
`Δp` or `k_R`, for which the paper states none. -/
structure Standing : Prop where
  lamD_pos : 0 < P.lamD
  alpha_nonneg : 0 ≤ P.alpha
  alpha_le_one : P.alpha ≤ 1
  lamL_nonneg : 0 ≤ P.lamL
  lamP_nonneg : 0 ≤ P.lamP
  rho_pos : 0 < P.rho
  cD_pos : 0 < P.cD
  m_pos : 0 < P.m
  c_le_cL : P.c ≤ P.cL

/-- Rate of transaction errors `λ_E = αλ_D` (p.8). -/
def lamE : ℝ := P.alpha * P.lamD

/-- Rate of correctly recorded demand `λ_D̂ = (1 − α)λ_D` (p.8). -/
def lamDhat : ℝ := (1 - P.alpha) * P.lamD

/-- Rate of unobserved stock reductions `λ_L̂ = λ_L + λ_E = λ_L + αλ_D` (p.12). -/
def lamLhat : ℝ := P.lamL + P.lamE

/-- The **generator** `M` of the unnormalized belief flow, indexed by the shelf stock
`q ∈ {0, …, q_m}` (index `0` = empty shelf, `Fin.last q_m` = full shelf):
`(Mψ)_q = λ_L̂ ψ_{q+1} 1{q < q_m} − (λ_L̂ + λ_D̂) ψ_q 1{q > 0}`.
Unobserved stock reductions (loss, mis-recorded sales) move mass from `q + 1` to `q`; a correctly
recorded sale (rate `λ_D̂`, only when in stock) ends the event-free trajectory.

**Formalization Note.** The paper writes the belief as `(Π_{q_m}, …, Π_0)ᵀ` (top to bottom,
p.12); here index `q` is the stock level `q` itself. -/
def generator : Matrix (Fin (P.qm + 1)) (Fin (P.qm + 1)) ℝ :=
  fun q r =>
    (if r.val = q.val + 1 then P.lamLhat else 0) -
      (if r = q ∧ 0 < q.val then P.lamLhat + P.lamDhat else 0)

/-- The **unnormalized flow** `ψ^F(s) = exp(sM) F`: `ψ^F_q(s)` is the probability that the stock
is `q` at time `s` and no correctly recorded sale occurred in `[0, s]`, started from the stock
distribution `F`. -/
noncomputable def unnormFlow (F : Fin (P.qm + 1) → ℝ) (s : ℝ) : Fin (P.qm + 1) → ℝ :=
  (NormedSpace.exp (s • P.generator)).mulVec F

/-- The **belief flow** of equation (1) (p.12): `Π^F(s) = ψ^F(s) / Σ_q ψ^F_q(s)`, the shelf
inventory distribution `s` time units after the last observable event when that event left the
belief `F` and no further observable event has occurred.

**Formalization Note.** Equation (1) is the nonlinear ODE
`Π̇_q = λ_L̂ Π_{q+1} 1{q<q_m} − λ_L̂ Π_q 1{q>0} + λ_D̂ Π_0 1{q=0} − λ_D̂ Π_0 Π_q` with
`Π(0) = F`; its solution is written here in closed linear form (normalized matrix exponential).
Differentiating `ψ/Σψ` with `(Σψ)' = −λ_D̂ (Σψ − ψ_0)` gives exactly (1). For `F` in the simplex
the denominator is positive. -/
noncomputable def flow (F : Fin (P.qm + 1) → ℝ) (s : ℝ) : Fin (P.qm + 1) → ℝ :=
  fun q => P.unnormFlow F s q / ∑ r, P.unnormFlow F s r

/-- The **intensity of observable events** at belief `b`:
`h(b) = λ_D̂ (1 − b_0) + λ_P` (a correctly recorded sale while in stock, or a phantom sale;
denominator of (2), p.13). -/
def hazard (b : Fin (P.qm + 1) → ℝ) : ℝ :=
  P.lamDhat * (1 - b 0) + P.lamP

/-- The **Bayes jump** (2) (p.13): the belief right after an observable event, from the belief
`b = Π(ι⁻)` just before it,
`J(b)_q = (λ_D̂ b_{q+1} 1{q < q_m} + λ_P b_q) / (λ_D̂ (1 − b_0) + λ_P)`.

**Formalization Note.** When the denominator `h(b)` is `0` no observable event can occur; Lean's
`x / 0 = 0` then returns the zero vector, which every use multiplies by `h(b) = 0` or excludes. -/
noncomputable def jump (b : Fin (P.qm + 1) → ℝ) : Fin (P.qm + 1) → ℝ :=
  fun q =>
    (P.lamDhat * (if h : q.val + 1 < P.qm + 1 then b ⟨q.val + 1, h⟩ else 0) + P.lamP * b q) /
      P.hazard b

/-- **Survival function of the next observable event** `ι` from belief `F`:
`S^F(s) = P(ι > s) = e^{−λ_P s} Σ_q ψ^F_q(s)` (no phantom sale and no correctly recorded sale in
`[0, s]`). Its hazard rate at `s` is `h(Π^F(s))`. The paper leaves the law of `ι` in (4)
implicit; this is it, written out. -/
noncomputable def survival (F : Fin (P.qm + 1) → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-P.lamP * s) * ∑ q, P.unnormFlow F s q

/-- The post-restock belief `1{q = q_m}` (full shelf, p.11 and p.13). -/
noncomputable def fullShelf : Fin (P.qm + 1) → ℝ :=
  Pi.single (Fin.last P.qm) 1

/-- **Shelf inventory distributions**: the beliefs reachable from the post-restock belief
`1{q = q_m}` by the dynamics (1)–(2) (proof of Theorem 1, p.35: "these inequalities do hold at any
restocking time … all subsequent inventory distributions are obtained from 1{q=qm} using the
dynamics described in Equation (1)–(2)"). Closed under the flow for any elapsed time `s ≥ 0`, and
under the jump at any belief where an observable event can occur (`h > 0`). -/
inductive Reachable : (Fin (P.qm + 1) → ℝ) → Prop
  | full : Reachable P.fullShelf
  | flow {G : Fin (P.qm + 1) → ℝ} (s : ℝ) : Reachable G → 0 ≤ s → Reachable (P.flow G s)
  | jump {G : Fin (P.qm + 1) → ℝ} : Reachable G → 0 < P.hazard G → Reachable (P.jump G)

/-- **Belief after an observed history**: from the belief `G`, with gaps `d_1, …, d_k` between
consecutive observable events and elapsed time `t` since the last one,
`path G [d_1, …, d_k] t = Π^{J(Π^{⋯J(Π^G(d_1))⋯}(d_k))}(t)` — flow `d_1`, jump, …, flow `d_k`,
jump, then flow `t`. -/
noncomputable def path : (Fin (P.qm + 1) → ℝ) → List ℝ → ℝ → (Fin (P.qm + 1) → ℝ)
  | G, [], t => P.flow G t
  | G, d :: ds, t => path (P.jump (P.flow G d)) ds t

end Params

end RecordInaccuracy


