-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_CPUGS
-- name    : GamblersFallacy_Supplement_CPUGS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:14:26.04368+00:00
-- url     : https://prove2.me/theorems/2f957ec7-f6dd-4622-8a10-73995a33a50a
-- title:
--   The staggered base stock policy and its finite-horizon cost per unit of goods sold (CPUGS)
-- statement:
--   Demands arrive in cycles. Cycle $t\ge1$ has inter-arrival time $Z_t\in\{1,2,\dots\}$ and nonzero demand size $Y_t$, and the process starts right after a nonzero demand at time $0$. Let $h,b$ be the unit holding and shortage costs. The **staggered base stock (SBS) policy** raises the inventory to $S_\ell$ at the beginning of each period with elapsed time $\ell$ since the last demand. A cycle with inter-arrival time $j$ and demand $y$ therefore costs
--   $$
--   C_{yj}=\sum_{\ell=1}^{j-1}hS_\ell+h(S_j-y)^++b(y-S_j)^+ .
--   $$
--
--   Over $n$ periods, let $\tau=\max\{t:Z_1+\dots+Z_t\le n-1\}$. Let $X_n$ be the demand in period $n$: $X_n=Y_{\tau+1}$ if the $(\tau+1)$-th demand arrives at $n$, and $0$ otherwise. The **cost per unit of goods sold** is
--   $$
--   \mathrm{CPUGS}=\frac{C_1+\dots+C_\tau+C_{\mathrm{tail}}}{Y_1+\dots+Y_\tau+\max\{1,X_n\}},\qquad C_t=C_{Y_tZ_t}.
--   $$
--   $C_{\mathrm{tail}}$ is the cost from period $Z_1+\dots+Z_\tau+1$ to $n$. It is $C_{Y_{\tau+1}Z_{\tau+1}}$ if the next demand arrives at $n$. Otherwise it is the holding cost $h\sum_{\ell=1}^{n-(Z_1+\dots+Z_\tau)}S_\ell$ of the truncated last cycle, which sells nothing. The paper's objective is the expected CPUGS.
--
--   The module also defines the **truncated-cycle holding term**
--   $$
--   \chi(X_n=0)\,\frac{h\sum_{\ell=1}^{n-(Z_1+\dots+Z_\tau)}S_\ell}{Y_1+\dots+Y_\tau+1},
--   $$
--   which is the share of the CPUGS contributed by a truncated last cycle. The identities of Theorems 4 and 5 omit it as printed, and their corrected forms add it.
--
--   **Formalization Note** Everything is defined pointwise on an outcome $\omega$ from sequences `Z : ℕ → Ω → ℕ` and `Y : ℕ → Ω → ℝ` (index $t\ge1$). $\tau$ is the greatest $t\le n$ with $Z_1+\dots+Z_t\le n-1$. This is the paper's maximum, because inter-arrival times are at least $1$ almost surely.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §4.2.2, p.19 (SBS policy) and p.20 (CPUGS, τ, C_tail, max{1, X_n}); Theorem 4, p.21 (Y_t); cycle cost C_kj, EC.2.4, p.ec5, and C_θj, EC.2.5, p.ec6

import Mathlib

namespace GamblersFallacy.Supplement

/-! The finite-horizon cost per unit of goods sold (CPUGS) of the staggered base stock policy,
§4.2.2, pp.19–21 of S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in
Intermittent Demand Management*, MSOM (2023), doi:10.1287/msom.2023.1217. Cycle `t ≥ 1` has
inter-arrival time `Z t` and demand size `Y t`; the process starts right after a nonzero demand at
time `0`. These definitions are pointwise in the outcome `ω`; the demand law enters only through
the hypotheses of Theorems 4 and 5. -/

variable {Ω : Type*}

/-- The arrival time `Z₁ + ⋯ + Z_t` of the `t`-th demand (`0` for `t = 0`). -/
def arrivalTime (Z : ℕ → Ω → ℕ) (t : ℕ) (ω : Ω) : ℕ :=
  ∑ s ∈ Finset.Icc 1 t, Z s ω

/-- **`τ = max{t : Z₁ + ⋯ + Z_t ≤ n − 1}`** (p.20), the number of demands in the periods
`1, …, n − 1`.

**Formalization Note.** Computed as the greatest `t ≤ n` with `Z₁ + ⋯ + Z_t ≤ n − 1`; since every
inter-arrival time is at least `1` almost surely, `Z₁ + ⋯ + Z_t ≥ t`, so no `t > n − 1` qualifies
and this is the paper's maximum (`t = 0` always qualifies for `n ≥ 1`). -/
def lastCycle (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : ℕ :=
  Nat.findGreatest (fun t => arrivalTime Z t ω ≤ n - 1) n

/-- Whether a demand arrives in the last period `n`: the `(τ + 1)`-th demand arrives at `n`. -/
def arrivesAtHorizon (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : Prop :=
  arrivalTime Z (lastCycle Z n ω + 1) ω = n

instance (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : Decidable (arrivesAtHorizon Z n ω) :=
  inferInstanceAs (Decidable (_ = _))

/-- **`X_n`, the demand in period `n`** (p.20): the size `Y_{τ+1}` of the `(τ + 1)`-th demand if it
arrives at `n`, and `0` otherwise. -/
noncomputable def demandAtHorizon (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if arrivesAtHorizon Z n ω then Y (lastCycle Z n ω + 1) ω else 0

/-- **The SBS cycle cost** `C_{yj} = Σ_{ℓ=1}^{j−1} h S_ℓ + h(S_j − y)⁺ + b(y − S_j)⁺` of a cycle with
inter-arrival time `j` and demand size `y` (Theorem 4, (3), p.21; EC.2.4, p.ec5; EC.2.5, p.ec6).
Under the staggered base stock policy (p.19) the inventory is raised to `S_ℓ` at the beginning of
a period with elapsed time `ℓ`; the periods `1, …, j − 1` of the cycle carry no demand and hold
`S_ℓ`, and in period `j` the demand `y` meets the level `S_j`. -/
noncomputable def sbsCycleCost (h b : ℝ) (S : ℕ → ℝ) (y : ℝ) (j : ℕ) : ℝ :=
  h * (∑ l ∈ Finset.Icc 1 (j - 1), S l) + h * max (S j - y) 0 + b * max (y - S j) 0

/-- **`C_tail`, the cost from period `Z₁ + ⋯ + Z_τ + 1` to period `n`** (p.20). If the next demand
arrives at `n` it is the full cycle cost `C_{Y_{τ+1}, Z_{τ+1}}`. Otherwise the last cycle is
truncated: no demand arrives in its `n − (Z₁ + ⋯ + Z_τ)` periods, and it costs the holding cost
`h Σ_{ℓ=1}^{n − (Z₁+⋯+Z_τ)} S_ℓ` ("holding cost occurs without any goods sold in the last cycle",
p.20). -/
noncomputable def tailCost (h b : ℝ) (S : ℕ → ℝ) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  if arrivesAtHorizon Z n ω then
    sbsCycleCost h b S (Y (lastCycle Z n ω + 1) ω) (Z (lastCycle Z n ω + 1) ω)
  else h * ∑ l ∈ Finset.Icc 1 (n - arrivalTime Z (lastCycle Z n ω) ω), S l

/-- **The CPUGS over `n` periods** (§4.2.2, p.20):
`(C₁ + ⋯ + C_τ + C_tail) / (Y₁ + ⋯ + Y_τ + max{1, X_n})`, where `C_t = C_{Y_t, Z_t}` is the cost
of the `t`-th cycle; its expectation is the paper's `E[C(π_sd)]`.

**Formalization Note.** The paper writes the denominator as `X_{Z₁} + ⋯ + X_{Z₁+⋯+Z_τ} +
max{1, X_n}`; the demand in period `Z₁ + ⋯ + Z_t` is `Y_t` (Theorem 4, p.21). -/
noncomputable def cpugs (h b : ℝ) (S : ℕ → ℝ) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ((∑ t ∈ Finset.Icc 1 (lastCycle Z n ω), sbsCycleCost h b S (Y t ω) (Z t ω)) +
      tailCost h b S Z Y n ω) /
    ((∑ t ∈ Finset.Icc 1 (lastCycle Z n ω), Y t ω) + max 1 (demandAtHorizon Z Y n ω))

/-- **The truncated-cycle holding term** (not in the paper; the correction of Theorems 4 and 5):
`χ(no demand at n) · h Σ_{ℓ=1}^{n − (Z₁+⋯+Z_τ)} S_ℓ / (Y₁ + ⋯ + Y_τ + 1)`, the share of the
CPUGS contributed by a truncated last cycle (`max{1, X_n} = 1` when `X_n = 0`). The printed
identities (3) and Theorem 5 omit it although `C_tail` includes it by the definition on p.20. -/
noncomputable def truncatedHolding (h : ℝ) (S : ℕ → ℝ) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  if arrivesAtHorizon Z n ω then 0
  else (h * ∑ l ∈ Finset.Icc 1 (n - arrivalTime Z (lastCycle Z n ω) ω), S l) /
    ((∑ t ∈ Finset.Icc 1 (lastCycle Z n ω), Y t ω) + 1)

end GamblersFallacy.Supplement


