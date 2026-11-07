-- Prove2me | Definitions.Def_AlmostMMS_fracH
-- name    : AlmostMMS_fracH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:30.029259+00:00
-- url     : https://prove2.me/theorems/91bd4167-0f90-4839-a07a-573ed3e82bf9
-- title:
--   Definitions 2.13–2.16, 3.5, Theorem 3.2 — fractional head profiles, $H$, $T$, $\tau$, $I$, $X$, $\rho$
-- statement:
--   Let $\Pi$ be a finite collection of head profiles containing $\emptyset$ and $\bot$. A **fractional head profile** of agent $i$ is a function $x_i$ with $x_i(\pi)\ge0$ for $\pi\in\Pi$ and $\sum_{\pi\in\Pi}x_i(\pi)=1$. For $x=\{x_i\}_{i\in N}$ the module defines
--   $$
--   H(x,\Pi,\ell)=\sum_{i}\sum_{\pi\in\Pi}x_i(\pi)P_i(\pi,\ell),\quad
--   T(x,\Pi,\ell)=\sum_{i}\sum_{\pi\in\Pi}x_i(\pi)\tau_i(\pi)(\ell-h_i)_+,
--   $$
--   $$
--   \tau(x,\Pi)=\sum_{i}\sum_{\pi\in\Pi}x_i(\pi)\tau_i(\pi),\quad
--   I(x,\Pi)=\sum_{i}\sum_{\pi\ne\bot}x_i(\pi),
--   $$
--   the number $X=|\{(i,\pi):0<x_i(\pi)<1\}|$ of strictly fractional entries, and the rounding loss
--   $$
--   \rho(q,\delta,X)=8+4\log_\lambda\max\Big\{1,\frac1\delta h_{\max}T_{\max}X\tau(x,\Pi)\Big\}+8q\log X,
--   $$
--   with $h_{\max}=\max_i h_i$ and $T_{\max}=\max_i T_i$.
--
--   **Formalization Note** $\log$ is base $2$ (p.55). The maximum $T_{\max}$ is a real supremum over the finite type of agents, and is $0$ when there are no agents.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definitions 2.13–2.16, pp.16–17; Definition 3.5, p.23; Theorem 3.2, p.25

import Mathlib
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit

namespace AlmostMMS

open Finset

/-- **Shared profile set** (Definition 2.13, p.16; Theorem 3.2, p.25): a finite collection of head
profiles that contains the empty profile `∅` (`some 0`) and the no-profile `⊥` (`none`).
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
def IsProfileSet (q : ℕ) (Ps : Finset (Option (Multiset ℝ))) : Prop :=
  none ∈ Ps ∧ some 0 ∈ Ps ∧ ∀ p, some p ∈ Ps → IsHeadProfile q p

/-- **Fractional profiles** (Definition 2.13, p.16): `x_i(π) ≥ 0` for `π ∈ Π` and
`∑_{π ∈ Π} x_i(π) = 1`, for every agent `i`. -/
def IsFractionalProfile {n : ℕ} (Ps : Finset (Option (Multiset ℝ)))
    (x : Fin n → Option (Multiset ℝ) → ℝ) : Prop :=
  ∀ i, (∀ π ∈ Ps, 0 ≤ x i π) ∧ ∑ π ∈ Ps, x i π = 1

/-- **Total fractional prefix head load** `H(x, Π, ℓ)` (Definition 2.14, p.16). -/
noncomputable def fracH {n m : ℕ} (v : Fin n → Fin m → ℝ) (Ps : Finset (Option (Multiset ℝ)))
    (x : Fin n → Option (Multiset ℝ) → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ i, ∑ π ∈ Ps, x i π * (optLoad v i π ℓ : ℝ)

/-- **Total fractional prefix tail load** `T(x, Π, ℓ)` (Definition 3.5, p.23). The truncated natural
subtraction `ℓ - h_i`, cast to `ℝ`, is `(ℓ - h_i)₊`. -/
noncomputable def fracT {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) (Ps : Finset (Option (Multiset ℝ)))
    (x : Fin n → Option (Multiset ℝ) → ℝ) (ℓ : ℕ) : ℝ :=
  ∑ i, ∑ π ∈ Ps, x i π * tauOf v q i π * ((ℓ - headCount v q i : ℕ) : ℝ)

/-- **Total fractional tail load** `τ(x, Π)` (Definition 2.15, p.17). -/
noncomputable def fracTau {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ)
    (Ps : Finset (Option (Multiset ℝ))) (x : Fin n → Option (Multiset ℝ) → ℝ) : ℝ :=
  ∑ i, ∑ π ∈ Ps, x i π * tauOf v q i π

/-- **Fractional number of assigned profiles** `I(x, Π)` (Definition 2.16, p.17). -/
noncomputable def fracI {n : ℕ} (Ps : Finset (Option (Multiset ℝ)))
    (x : Fin n → Option (Multiset ℝ) → ℝ) : ℝ :=
  ∑ i, ∑ π ∈ Ps with π ≠ none, x i π

open Classical in
/-- The number `X = |{(i, π) : 0 < x_i(π) < 1}|` of strictly fractional entries (Theorem 3.2, p.25). -/
noncomputable def fracX {n : ℕ} (Ps : Finset (Option (Multiset ℝ)))
    (x : Fin n → Option (Multiset ℝ) → ℝ) : ℕ :=
  ((univ ×ˢ Ps).filter fun p => 0 < x p.1 p.2 ∧ x p.1 p.2 < 1).card

/-- **The rounding loss** `ρ(q, δ, X) = 8 + 4 log_λ max{1, (1/δ) h_max T_max X τ(x, Π)} + 8q log X`
(Theorem 3.2, p.25), with `h_max = max_i h_i` and `T_max = max_i T_i`.

**Formalization Note.** The paper's `log` is base `2` (p.55 bounds `K` through `X · 2^{-(K-1)}`) and
`log_λ` is `Real.logb λ`. The real `⨆` runs over the finite type `Fin n`, so it is the maximum; it is
`0` when there are no agents, a case in which nothing is rounded. `Real.logb 2 0 = 0` at `X = 0`,
where `x` is integral already. -/
noncomputable def rhoRound {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ)
    (Ps : Finset (Option (Multiset ℝ))) (x : Fin n → Option (Multiset ℝ) → ℝ) (δ lam : ℝ) : ℝ :=
  8 + 4 * Real.logb lam (max 1 ((1 / δ) * ((univ.sup (headCount v q) : ℕ) : ℝ) *
      (⨆ i, tailVal v q i) * (fracX Ps x : ℝ) * fracTau v q Ps x))
    + 8 * (q : ℝ) * Real.logb 2 (fracX Ps x : ℝ)

end AlmostMMS


