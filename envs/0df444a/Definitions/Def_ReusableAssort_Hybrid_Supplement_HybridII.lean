-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Supplement_HybridII
-- name    : ReusableAssort_Hybrid_Supplement_HybridII
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:15:53.089846+00:00
-- url     : https://prove2.me/theorems/3fa2f150-f8df-48bf-8b20-028cfd58e4d0
-- title:
--   Sim+Hybrid(ii), p. 20 — per-step switch between Algorithms 2 and 3 by expected revenue-to-go
-- statement:
--   Sim+Hybrid(ii) (p. 20). Fix an LP solution $y$, a random-discard probability $\gamma$ for Algorithm 2, and a tie-break rule $\mathrm{tb}$. At each time $t$, before the type $z_t$ is revealed, let $J$ be the current state (units out and their return times). Let $E_2(t, J)$ and $E_3(t, J)$ be the exact expected revenues from time $t$ to $T$ of Algorithm 2 (with $\gamma$) and of Algorithm 3, each run with $y$ from time $t$ in state $J$. Sim+Hybrid(ii) runs Algorithm 2 for time $t$ if $E_2(t,J) > E_3(t,J)$, Algorithm 3 if $E_2(t,J) < E_3(t,J)$, and the algorithm chosen by $\mathrm{tb}(t, J)$ on a tie. Running the chosen algorithm for one step means: a product with no unit on hand is removed; otherwise it is kept with probability $1-\gamma$ (Algorithm 2) or kept iff $r^{z_t}_i \ge P^{z_t}_{i,t}$ (Algorithm 3); then Sub-assortment Sampling is applied.
--
--   The expected revenue $\mathbb E[\mathrm{Rev}_{\mathrm{H(ii)}}]$ is that of this process from time $1$ with no unit out.
--
--   This is the method of conditional expectations ("Be-The-Leader") applied to the two algorithms.
--
--   **Formalization Note** The paper estimates $E_2$ and $E_3$ by Monte-Carlo simulation; the definition uses the exact conditional expectations, which is what the proof of Theorem 4 compares.
--
--   The function `expRevHybridIIFrom` gives the same process from any specified time and outstanding-return state; `expRevHybridII` uses time 1 and no outstanding rentals.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 20, 'Monte-Carlo simulation to help' and proof sketch of Theorem 4 (pp. 20–21)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Supplement_Process

namespace ReusableAssort.Hybrid.Supplement

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- The switch of Sim+Hybrid(ii) (p. 20) at time `t` in state `J` (outstanding returns): `true`
runs Algorithm 2 (random discarding with probability `γ`), `false` runs Algorithm 3, whichever
has the higher exact expected revenue from `t` to `T` when started at time `t` in state `J`;
a tie is broken by `tb t J`. -/
noncomputable def useAlg2 (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (γ : ℝ)
    (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) (t : ℕ) (J : Fin n → ℕ → ℕ) : Bool :=
  let e2 := expRev I y (alg2 γ) t J
  let e3 := expRev I y (alg3 I y) t J
  if e3 < e2 then true else if e2 < e3 then false else tb t J

/-- Keep probability of product `i` at step `k` under Sim+Hybrid(ii): `0` if no unit of `i` is
on hand, else the keep probability of the inner rule of the algorithm selected by `useAlg2` at
the current time and state. -/
noncomputable def hybridIIKeep (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (γ : ℝ)
    (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (k : Fin (T + 1 - t₀)) (v : Fin (T + 1 - t₀) → Step n T Z) (i : Fin n) : ℝ :=
  let t := t₀ + k.1
  let rule : Fin n → Rule Z :=
    if useAlg2 I y γ tb t (retState t₀ ret v k.1) then alg2 γ else alg3 I y
  if onHand I t₀ ret v i k.1 = 0 then 0 else keep I i (rule i) t (v k).1

/-- Conditional revenue-to-go of Sim+Hybrid(ii), from time `t₀` and outstanding-return
state `ret`; this is the quantity compared with both component policies in the proof sketch. -/
noncomputable def expRevHybridIIFrom (I : Instance n T Z)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (γ : ℝ)
    (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) : ℝ :=
  expRevA I y t₀ (hybridIIKeep I y γ tb t₀ ret)

/-- Expected revenue of Sim+Hybrid(ii) over times `1, …, T`, started with no unit out. -/
noncomputable def expRevHybridII (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (γ : ℝ) (tb : ℕ → (Fin n → ℕ → ℕ) → Bool) : ℝ :=
  expRevHybridIIFrom I y γ tb 1 (fun _ _ => 0)

end ReusableAssort.Hybrid.Supplement


