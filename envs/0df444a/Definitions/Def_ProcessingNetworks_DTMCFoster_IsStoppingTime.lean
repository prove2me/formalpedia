-- Prove2me | Definitions.Def_ProcessingNetworks_DTMCFoster_IsStoppingTime
-- name    : ProcessingNetworks_DTMCFoster_IsStoppingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:28.885199+00:00
-- url     : https://prove2.me/theorems/4290a942-810a-4192-a6cc-4dfa0310da76
-- title:
--   Stopping time with respect to a discrete-time Markov chain (§C.2)
-- statement:
--   Let $X=\{X_k : k\in\mathbb Z_+\}$ be an $\mathcal S$-valued stochastic process on a probability space $(\Omega,\mathbb P)$. A function $\tau:\Omega\to\mathbb Z_+\cup\{\infty\}$ is a **stopping time with respect to $X$** if, for each integer $k\ge 0$, the event $\{\omega\in\Omega:\tau(\omega)\le k\}$ is a union of cylinder sets
--   $$
--   \{\omega\in\Omega : X_0=i_0,\ X_1=i_1,\ \dots,\ X_k=i_k\},\qquad i_0,\dots,i_k\in\mathcal S .
--   $$
--   Equivalently, there is a set $A\subseteq\mathcal S^{k+1}$ of paths such that $\{\tau\le k\}=\{(X_0,\dots,X_k)\in A\}$: whether $\tau$ has occurred by time $k$ is decided by $X_0,\dots,X_k$ alone.
--
--   This is the class of random times in the comparison theorem (Lemma C.24), which is applied with first passage times and with truncations of them.
--
--   **Formalization Note** Paths of length $k+1$ are functions $\mathrm{Fin}(k+1)\to S$; $\tau$ takes values in $\mathbb N_\infty$. No measurability condition is added: with measurable $X_k$ on a countable state space, the events $\{\tau\le k\}$ are automatically measurable.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, §C.2 Strong Markov property, p.276 (PDF p.292)

import Mathlib

namespace ProcessingNetworks.DTMCFoster

/-- **Stopping time with respect to a discrete-time process** (Dai & Harrison, *Processing
Networks*, pre-publication draft 2020-4-2, spnbook.org, Appendix C, §C.2, p.276, PDF p.292):
"A function `τ : Ω → ℤ₊ ∪ {∞}` is said to be a stopping time with respect to `X` if, for each
integer `k ≥ 0`, the set `{ω ∈ Ω : τ(ω) ≤ k}` can be written as the union of sets having the form
`{ω ∈ Ω : X₀ = i₀, X₁ = i₁, …, X_k = i_k}`, where `i₀, i₁, …, i_k ∈ 𝒮`."

`IsStoppingTime X τ` says: for every `k`, there is a set `A` of paths `(i₀, …, i_k)` such that
`{τ ≤ k}` is exactly the set of `ω` whose initial path `(X₀(ω), …, X_k(ω))` lies in `A`.

**Formalization Note** A union of the cylinder sets `{X₀ = i₀, …, X_k = i_k}` is the same thing as
the preimage of a set `A ⊆ 𝒮^{k+1}` of paths under `ω ↦ (X₀(ω), …, X_k(ω))`; paths of length
`k + 1` are functions `Fin (k + 1) → S`. `τ` takes values in `ℕ∞ = ℤ₊ ∪ {∞}`. No measurability
condition is added: on a countable state space with measurable `X_k` the sets `{τ ≤ k}` are then
automatically measurable. -/
def IsStoppingTime {S Ω : Type*} (X : ℕ → Ω → S) (τ : Ω → ℕ∞) : Prop :=
  ∀ k : ℕ, ∃ A : Set (Fin (k + 1) → S),
    {ω | τ ω ≤ (k : ℕ∞)} = {ω | (fun l : Fin (k + 1) => X (l : ℕ) ω) ∈ A}

end ProcessingNetworks.DTMCFoster


