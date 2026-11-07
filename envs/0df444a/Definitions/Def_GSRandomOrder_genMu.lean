-- Prove2me | Definitions.Def_GSRandomOrder_genMu
-- name    : GSRandomOrder_genMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:01:44.472205+00:00
-- url     : https://prove2.me/theorems/0584bd94-9e45-4521-a834-b4ba6cd21916
-- title:
--   The generalized thought experiment: $\phi_\tau$, $\phi^{-f}_\tau$ and $\tilde\mu$
-- statement:
--   Fix a valuation $v$. The **generalized thought experiment** takes as inputs two times $1/e\le t_0\le t\le 1$, a set $S$ of **reshuffled** items with independent timestamps $\tau_g\sim\mathrm{Unif}[0,t_0]$, and a set $B$ of **pinned** items, disjoint from $S$, with fixed timestamps $\beta_g\in[1/e,t]$.
--
--   1. *Reshuffle.* The set present at time $\tau\in[0,t]$ is $U_\tau=S_\tau\cup B_\tau$, with $S_\tau=\{g\in S:\tau_g\le\tau\}$ and $B_\tau=\{g\in B:\beta_g\le\tau\}$. A reshuffled item with $\tau_g\le1/e$ is early.
--   2. *Replay.* The death time of an early item is $\sigma_g=\min(\{\tau\in[1/e,t]:g\notin D_v(U_\tau)\}\cup\{t\})$.
--   3. *Retain.* Each early item is independently added to $R$ with probability $\ln(e\sigma_g)$. Pinned items are never retained.
--
--   With the timestamps fixed and $\theta_g=\ln(e\sigma_g)$ for early items, $\theta_g=0$ for reshuffled items that are not early,
--   $$
--   \phi_\tau=\prod_{g\in A}\theta_g\prod_{g\in S\setminus A}(1-\theta_g),\qquad \phi^{-f}_\tau=\prod_{g\in A}\theta_g\prod_{g\in S\setminus(A+f)}(1-\theta_g),
--   $$
--   and $\mathbb E_\tau\phi_\tau$ is the probability that $R=A$. For a **moving item** $x\notin S\cup B$ pinned at $\tilde\tau\in[1/e,t]$ in addition to $B$, this probability is $\tilde\mu(\tilde\tau)$.
--
--   With $t_0=t$ and $B=\emptyset$ this is the thought experiment defining the survival law. It is the object of the induction that proves the comparison inequality.
--
--   **Formalization Note** The pinned timestamps are a function $\beta$ read only on $B$; for the moving item, $\beta$ is updated at $x$ to $\tilde\tau$ and $x$ is added to the pinned set. The conditions $1/e\le t_0\le t\le 1$, $B\cap S=\emptyset$ and $\beta_g\in[1/e,t]$ are hypotheses of the theorems. The timestamps are $\tau_g=t_0r_g$ with $r$ uniform on $[0,1]^n$; the expectation is a Bochner integral of a bounded measurable function, and it is $0$ when $A\not\subseteq S$.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §B.1, pp.21–22 (the generalized thought experiment, eq. (18), the functions φ_τ, φ^{−f}_τ and μ̃)

import Mathlib
import Definitions.Def_GSRandomOrder_survivalLaw

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder

/-- The set present at time `s` in the generalized thought experiment (§B.1 step 1, p.22):
`U_s = S_s ∪ B_s`, with `S_s = {g ∈ S : τ_g ≤ s}` and `B_s = {g ∈ B : β_g ≤ s}`. -/
noncomputable def presentGen {n : ℕ} (S B : Finset (Fin n)) (β τ : Fin n → ℝ) (s : ℝ) :
    Finset (Fin n) :=
  presentAt S τ s ∪ presentAt B β s

/-- `ϕ_τ` of (18), p.22: with the timestamps `τ` of the reshuffled items `S` and the pinned
timestamps `β` of the items of `B` fixed, the probability that the retained set equals `A`,
`Π_{g ∈ A} θ_g · Π_{g ∈ S \ A} (1 − θ_g)`, where `θ_g = ln(e σ_g)` for an early reshuffled item
(`τ_g ≤ 1/e`) with death time `σ_g = min({τ ∈ [1/e, t] : g ∉ D_u(U_τ)} ∪ {t})`, and `θ_g = 0` for
a reshuffled item that is not early. Pinned items are never retained. -/
noncomputable def genPhi {n : ℕ} (u : Finset (Fin n) → WithBot ℝ) (t : ℝ) (S B : Finset (Fin n))
    (β τ : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  retainProb u (presentGen S B β τ) t τ S A

/-- `ϕ^{−f}_τ` of p.22: for `f ∈ S \ A`, the probability that the items other than `f` produce
`A`, `Π_{g ∈ A} θ_g · Π_{g ∈ S \ (A + f)} (1 − θ_g)`. -/
noncomputable def genPhiMinus {n : ℕ} (u : Finset (Fin n) → WithBot ℝ) (t : ℝ)
    (S B : Finset (Fin n)) (β τ : Fin n → ℝ) (A : Finset (Fin n)) (f : Fin n) : ℝ :=
  (∏ g ∈ A, retention u (presentGen S B β τ) t τ g) *
    ∏ g ∈ S \ insert f A, (1 - retention u (presentGen S B β τ) t τ g)

/-- **The generalized thought experiment** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §B.1, pp.21–22): with times
`1/e ≤ t₀ ≤ t ≤ 1`, reshuffled items `S` with independent timestamps `τ_g ∼ Unif[0, t₀]`, and
pinned items `B` (disjoint from `S`) with fixed timestamps `β_g ∈ [1/e, t]`, the replay runs until
the horizon `t` and produces a random retained set `R ⊆ S`.
`genMu u t₀ t S B β A` is the probability that `R = A`, i.e. `E ϕ_τ` of (18).

The function `μ̃(τ̃)` of p.22 for a moving item `x ∉ S ∪ B` pinned at `τ̃` is
`genMu u t₀ t S (insert x B) (Function.update β x τ̃) A`.

**Formalization Note.** `β : Fin n → ℝ` is read only on `B`; the conditions `B ∩ S = ∅` and
`β_g ∈ [1/e, t]` for `g ∈ B`, as well as `1/e ≤ t₀ ≤ t ≤ 1`, are hypotheses of the theorems, not
part of the definition. The timestamps are `τ_g = t₀ · r_g` with `r` distributed by `volume` on
`Fin n → unitInterval` (i.i.d. uniform on `[0, 1]`), so that `τ_g ∼ Unif[0, t₀]`; the integrand is
a bounded measurable function of `r`, so the Bochner integral is the expectation. The value is
`0` when `A ⊄ S`. With `t₀ = t` and `B = ∅` this is the thought experiment of §3.2 (p.22). -/
noncomputable def genMu {n : ℕ} (u : Finset (Fin n) → WithBot ℝ) (t₀ t : ℝ)
    (S B : Finset (Fin n)) (β : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  if A ⊆ S then
    ∫ r : Fin n → unitInterval, genPhi u t S B β (fun g => t₀ * (r g : ℝ)) A
  else 0

end GSRandomOrder


