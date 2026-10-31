-- Prove2me | Definitions.Def_KashUpgrade_lumpBlock
-- name    : KashUpgrade_lumpBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:41.796412+00:00
-- url     : https://prove2.me/theorems/8ef352a0-5ea5-4e3f-9564-e731c4677e18
-- title:
--   The block $\mathcal L(i)$ of a lumping
-- statement:
--   Given a lumping $\mathcal L$ and an index $i$ with $j+1\le i\le j+n$,
--   $$
--   \mathcal L(i):=\{\ell\in\{j+1,\dots,j+n\}:\mathcal L\vdash\theta^j_\ell=\theta^j_i\}
--   $$
--   is the set of indices whose thresholds are lumped together with $\theta^j_i$.
--
--   **Formalization Note** The constraints in $\mathcal L$ entail $\theta_\ell=\theta_i$ exactly when every constraint $\theta_m=\theta_{m+1}$ between the two indices is in $\mathcal L$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (19), p.17

import Mathlib

namespace KashUpgrade

/-- **The block `L(i)`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (19), p.17:
`L(i) := {ℓ ∈ {j + 1, …, j + n} : L ⊢ θ_ℓ = θ_i}`, the set of indices whose thresholds are lumped
with `θ_i` in `L`.

**Formalization Note** The constraints in `L` entail `θ_ℓ = θ_i` exactly when every constraint between
the two indices is in `L`; `L` is the set of `m` such that `θ_m = θ_{m+1}` is in the lumping. -/
noncomputable def lumpBlock (j n : ℕ) (L : Finset ℕ) (i : ℕ) : Finset ℕ :=
  open Classical in
  (Finset.Icc (j + 1) (j + n)).filter fun ℓ => ∀ m, min ℓ i ≤ m → m < max ℓ i → m ∈ L

end KashUpgrade


