-- Prove2me | Definitions.Def_GoodProphets_seqProb
-- name    : GoodProphets_seqProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:48.460624+00:00
-- url     : https://prove2.me/theorems/2f5798a7-bc20-4c99-b840-6333ea0a66e8
-- title:
--   I.i.d. arrival sequences: probability of an event, $N_\theta(t)$, $\bar N_\theta(t)$, $N_\theta$
-- statement:
--   In each of the periods $1,\dots,T$ a type $\theta_i$ arrives, drawn independently from a probability vector $\vec p$ on the $k$ types. For an event $E$ about the arrival sequence,
--   $$
--   \mathbb P[E]=\sum_{(\theta_1,\dots,\theta_T)\in E}\ \prod_{i=1}^Tp_{\theta_i}.
--   $$
--   For a sequence and a period $t$ the module defines
--
--   1. $N_\theta(t)$, the number of type-$\theta$ arrivals in periods $[1,t]$;
--   2. $\bar N_\theta(t)$, the number of type-$\theta$ arrivals in periods $[t+1,T]$;
--   3. $N_\theta$, the number of type-$\theta$ arrivals over the whole horizon, so that $N_\theta(t)+\bar N_\theta(t)=N_\theta$.
--
--   These are the random quantities of the paper's concentration lemmas.
--
--   **Formalization Note** Period $i+1$ is the index $i$ of `Fin T`. The law is the finite product law. No measure space is used.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), §2, p.7, "Periods, Arrivals, and Types"

import Mathlib

namespace GoodProphets

open Classical in
/-- The probability of an event `E` about the arrival sequence `θ₁, …, θ_T` when the types are
drawn i.i.d. from `p` (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), §2, p.7, "Periods, Arrivals, and
Types"): `P[E] = ∑_{θ⃗ ∈ E} ∏ᵢ p_{θᵢ}`.

**Formalization Note** Period `i + 1` of the paper is the index `i : Fin T`. The law is the finite
product law on `Fin T → Fin k`; no measure space is used. -/
noncomputable def seqProb {k T : ℕ} (p : Fin k → ℝ) (E : (Fin T → Fin k) → Prop) : ℝ :=
  ∑ θs ∈ Finset.univ.filter E, ∏ i, p (θs i)

/-- `N_θ(t)`, the number of arrivals of type `θ` in periods `[1, t]` (doi:10.1287/mnsc.2023.04307,
p.7); periods `1, …, t` are the indices `0, …, t − 1`. -/
def countBefore {k T : ℕ} (θs : Fin T → Fin k) (t : ℕ) (θ : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin T => (i : ℕ) < t ∧ θs i = θ).card

/-- `N̄_θ(t)`, the number of arrivals of type `θ` after period `t`, i.e. in `[t + 1, T]`
(doi:10.1287/mnsc.2023.04307, p.7); these are the indices `t, …, T − 1`. -/
def countAfter {k T : ℕ} (θs : Fin T → Fin k) (t : ℕ) (θ : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin T => t ≤ (i : ℕ) ∧ θs i = θ).card

/-- `N_θ`, the number of arrivals of type `θ` over the entire horizon (doi:10.1287/mnsc.2023.04307,
p.7). -/
def countAll {k T : ℕ} (θs : Fin T → Fin k) (θ : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin T => θs i = θ).card

end GoodProphets


