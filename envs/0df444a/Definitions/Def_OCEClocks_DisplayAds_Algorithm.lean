-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_Algorithm
-- name    : OCEClocks_DisplayAds_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:24:04.35919+00:00
-- url     : https://prove2.me/theorems/ac78ee87-8907-44f6-a86e-9e2922b04bd3
-- title:
--   Display Ads: values, the maximum-weight matching benchmark, level measures (10), duals (12), offers (13), water filling and the expected value (§5.4)
-- statement:
--   **Display Ads (§5).** Advertisers $i\in\{0,\dots,m-1\}$ are known upfront, and impressions $j\in\{0,\dots,n-1\}$ arrive in order. On arrival, impression $j$ reveals weights $w_{ij}\ge0$ and is allocated to at most one advertiser. Advertisers have free disposal: the value of advertiser $i$ with assigned set $S_i$ is $\max_{j\in S_i}w_{ij}$, and $0$ if $S_i=\emptyset$. The objective is $\sum_i\max_{j\in S_i}w_{ij}$. The offline optimum $\mathrm{OPT}$ is the weight $\sum_{(i,j)\in M}w_{ij}$ of a maximum-weight matching $M$ (no advertiser and no impression used twice).
--
--   **Online Primal-Dual Allocation with First-Age Poisson OCEC (§5.4), rate $\lambda$.** Each advertiser $i$ keeps a measure $\nu_{i,\ell}$ on ages for every level $\ell>0$, initially $\pi$. With $\Gamma$ and $\Gamma^\star$ from (6), (7), the duals (12) are
--
--   $$\alpha_{i,\ell}=\Gamma^\star-\nu_{i,\ell}\Gamma,\qquad \alpha_i=\int_0^\infty\alpha_{i,\ell}\,d\ell .$$
--
--   When impression $j$ arrives, let $\alpha_i(y)$ be $i$'s dual after applying the update (10) once with mass $y\in[0,1]$:
--
--   $$\nu_{i,\ell}\leftarrow\begin{cases}\nu_{i,\ell}M_y,&\ell\le w_{ij},\\ \nu_{i,\ell}G_y,&\ell>w_{ij}.\end{cases}\qquad(10)$$
--
--   The **offer** (13) of $i$ at mass $y$ is $\Gamma^\star w_{ij}-\alpha_i(y)$. Impression $j$ is processed in three steps.
--
--   1. **Water filling.** Starting from $x_{ij}=0$, continuously allocate to the advertisers with the largest positive offer until $\sum_ix_{ij}=1$ or no positive offer remains. The outcome satisfies three conditions:
--      - $x_{ij}\ge0$ and $\sum_ix_{ij}\le1$;
--      - every advertiser with $x_{ij}>0$ has a nonnegative final offer that is the maximum of all final offers;
--      - if $\sum_ix_{ij}<1$, every final offer is $\le0$.
--   2. **Update.** Every $\nu_{i,\ell}$ is updated by (10) with $y=x_{ij}$.
--   3. **Round.** OCEC rounding with one independent First-Age Poisson generator per advertiser and discard clocks allocates $j$.
--
--   The **expected value** of an allocation $x$ is $\mathbb E\big[\sum_i\max_{j\in S_i}w_{ij}\big]$ over the generators' randomness and the discard clocks.
--
--   **Formalization Note** `advertiserValue`, `IsMatching` and `OPT` give the value and the benchmark. `OPT` is a supremum over the finite nonempty type of matchings, so it is a maximum. `levelMeasure λ (w i) (x i) ℓ k` is $\nu_{i,\ell}$ after the first $k$ impressions (the final measure for $k=n$). `levelDual`, `offlineDual`, `dualAfter` and `offer` are $\alpha_{i,\ell}$, $\alpha_i$, $\alpha_i(y)$ and (13); the level integrals are Lebesgue integrals over $(0,\infty)$, whose integrands vanish above the largest weight seen, since $\pi G_t=\pi$. Water filling is stated relationally (`IsWaterFillingStep`, `IsWaterFillingRun`): the allocation $x$ is deterministic, and the offers for $j$ are computed from the measures produced by $x$ on earlier impressions. In the third condition, advertisers with $x_{ij}>0$ then have offer exactly $0$, by the second. `expectedValue λ w x` integrates the total value over `roundingLaw (generatorLaw λ n) x`.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), pp. 13–14, §5 (problem, benchmark); p. 15, §5.3, eq. (10); pp. 16–17, §5.4 (algorithm box, eqs. (12), (13), water filling)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_OCEC
import Definitions.Def_OCEClocks_DisplayAds_Potential

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-!
# Display Ads and the Online Primal-Dual Allocation with First-Age Poisson OCEC (§5)

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), pp. 13–14 (§5, the problem and its benchmark), p. 15 (§5.3,
update (10)), pp. 16–17 (§5.4: duals (12), offers (13), water filling, rounding).

Advertisers are `Fin m`, impressions are `Fin n` in arrival order, and `w i j ≥ 0` is the weight
of impression `j` for advertiser `i`. A fractional allocation is `x : Fin m → Fin n → ℝ`.
-/

/-- The value `max_{j ∈ S} w_ij` of advertiser `i` with assigned impressions `S` (free disposal),
and `0` if `S` is empty (p. 14). -/
noncomputable def advertiserValue {m n : ℕ} (w : Fin m → Fin n → ℝ) (i : Fin m)
    (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then S.sup' h (w i) else 0

/-- A matching between advertisers and impressions: a set of pairs `(i, j)` in which no
advertiser and no impression occurs twice. -/
def IsMatching {m n : ℕ} (M : Finset (Fin m × Fin n)) : Prop :=
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

/-- The offline optimum (p. 14): the weight `Σ_{(i,j) ∈ M} w_ij` of a maximum-weight matching.
The supremum is over the finite, nonempty set of matchings (the empty matching is one), so it is
a maximum. -/
noncomputable def OPT {m n : ℕ} (w : Fin m → Fin n → ℝ) : ℝ :=
  ⨆ M : {M : Finset (Fin m × Fin n) // IsMatching M}, ∑ e ∈ M.1, w e.1 e.2

/-- One step of update (10) at level `ℓ` for an impression of weight `w_ij` allocated mass `y`:
`ν ↦ νM_y` if `ℓ ≤ w_ij` and `ν ↦ νG_y` if `ℓ > w_ij`. -/
noncomputable def levelUpdate (lam wij y ℓ : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  if ℓ ≤ wij then matchingKernelMeasure lam y ν else gapKernelMeasure lam y ν

/-- The age measure `ν_{i,ℓ}` of advertiser `i` (weights `wi = w i ·`, allocations `xi = x i ·`)
at level `ℓ` after the first `k` impressions (§5.3, p. 15): `π` initially, then update (10) for
each impression in arrival order. For `k ≥ n` it is the final measure. -/
noncomputable def levelMeasure {n : ℕ} (lam : ℝ) (wi xi : Fin n → ℝ) (ℓ : ℝ) : ℕ → Measure ℝ
  | 0 => stationaryAge lam
  | k + 1 =>
    if h : k < n then levelUpdate lam (wi ⟨k, h⟩) (xi ⟨k, h⟩) ℓ (levelMeasure lam wi xi ℓ k)
    else levelMeasure lam wi xi ℓ k

/-- The level dual `α_{i,ℓ} = Γ⋆ - ν_{i,ℓ}Γ` of a level measure (12). -/
noncomputable def levelDual (lam : ℝ) (ν : Measure ℝ) : ℝ :=
  targetRatio lam - ∫ a, potential lam a ∂ν

/-- The offline dual `α_i = ∫_0^∞ α_{i,ℓ} dℓ` (12) when impression `j` arrives. -/
noncomputable def offlineDual {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) : ℝ :=
  ∫ ℓ in Set.Ioi (0 : ℝ), levelDual lam (levelMeasure lam (w i) (x i) ℓ j)

/-- `α_i(y)`: advertiser `i`'s offline dual after applying (10) once with mass `y` to the measures
`ν_{i,ℓ}` held when impression `j` arrives (p. 17). -/
noncomputable def dualAfter {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) (y : ℝ) : ℝ :=
  ∫ ℓ in Set.Ioi (0 : ℝ),
    levelDual lam (levelUpdate lam (w i j) y ℓ (levelMeasure lam (w i) (x i) ℓ j))

/-- Advertiser `i`'s offer (13) to impression `j` at candidate mass `y`: `Γ⋆ w_ij - α_i(y)`. -/
noncomputable def offer {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (y : ℝ) : ℝ :=
  targetRatio lam * w i j - dualAfter lam w x i j y

/-- The outcome of water filling for impression `j` (step 1, pp. 16–17), stated relationally:
the masses `x_ij` are nonnegative with `Σ_i x_ij ≤ 1`; every advertiser receiving positive mass
has a nonnegative final offer that is the maximum final offer over all advertisers; and if `j` is
not fully allocated, every final offer is nonpositive (so those with positive mass are `0`). The
offers are computed from the measures produced by the allocations of earlier impressions. -/
def IsWaterFillingStep {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) (j : Fin n) : Prop :=
  (∀ i, 0 ≤ x i j) ∧ (∑ i, x i j ≤ 1) ∧
  (∀ i, 0 < x i j →
    0 ≤ offer lam w x i j (x i j) ∧ ∀ i', offer lam w x i' j (x i' j) ≤ offer lam w x i j (x i j)) ∧
  (∑ i, x i j < 1 → ∀ i, offer lam w x i j (x i j) ≤ 0)

/-- A run of the allocation rule: every impression is allocated by water filling. -/
def IsWaterFillingRun {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) : Prop :=
  ∀ j, IsWaterFillingStep lam w x j

/-- The expected total value `E[Σ_i max_{j ∈ S_i} w_ij]` when the allocation `x` is rounded by
OCEC rounding with independent First-Age Poisson generators of rate `λ`, one per advertiser,
and discard clocks (step 3, p. 16). -/
noncomputable def expectedValue {m n : ℕ} (lam : ℝ) (w x : Fin m → Fin n → ℝ) : ℝ :=
  ∫ ω, ∑ i, advertiserValue w i (allocated (firstAgeGenerator lam n) x ω i)
    ∂roundingLaw (generatorLaw lam n) x

end OCEClocks.DisplayAds


