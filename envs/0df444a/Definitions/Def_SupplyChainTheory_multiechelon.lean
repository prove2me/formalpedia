-- Prove2me | Definitions.Def_SupplyChainTheory_multiechelon
-- name    : SupplyChainTheory_multiechelon
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:16:07.143373+00:00
-- url     : https://prove2.me/theorems/6fb9c821-2af3-4baa-b352-711e19328931
-- title:
--   The serial multiechelon models of Chapter 6: echelon accounting, the Clark-Scarf recursion, the Shang-Song bounds, and the guaranteed-service serial cost
-- statement:
--   The serial-system models of Chapter 6 of Snyder and Shen: an $N$-stage serial supply chain,
--   stage $1$ facing the customer and stage $N$ ordering from an unlimited supplier.
--
--   **Echelon accounting (Sect. 6.2.1).** With local holding costs $h'_j$ (and $h'_{N+1} = 0$),
--   `echelonHolding N h' j` is the echelon holding cost $h_j = h'_j - h'_{j+1}$ of (6.4), and
--   `localHolding N h j` recovers $h'_j = \sum_{i=j}^N h_i$ from echelon costs (Table 6.1). With
--   local on-hand inventories $I'_i$ and in-transit inventories $IT_{i-1}$ (from $i$ to $i-1$,
--   $IT_0 = 0$), `echelonOnHand I' IT j` is stage $j$'s echelon on-hand inventory
--   $I_j = \sum_{i=1}^j (I'_i + IT_{i-1})$ of (6.1).
--
--   **The Clark-Scarf recursion (Sect. 6.2.2).** For echelon holding costs $h_j$, stockout cost
--   $p$ at stage 1, lead-time demand laws $D_j$ and an echelon base-stock vector $S$, the functions
--   (6.21)-(6.23) are `csBar N h p D S j` for $\bar g_j(x \mid S)$, `csHat N h p D S j` for
--   $\hat g_j(x \mid S) = h_j x + \bar g_{j-1}(x \mid S)$, and `csG N h p D S j` for
--   $g_j(y \mid S) = \mathbb{E}[\hat g_j(y - D_j \mid S)]$, starting from
--   $\bar g_0(x) = (p + h'_1) x^-$ and closing with $\bar g_j(x \mid S) = g_j(\min\{S_j, x\} \mid S)$.
--   The expected cost of the system under $S$ is $g_N(S_N \mid S)$. `CSSequential N h p D S`
--   says that $S$ is built by the sequential minimization (6.26): each $S_j$ minimizes
--   $g_j(\cdot \mid S)$, which depends only on $S_1, \dots, S_{j-1}$.
--
--   **The Shang-Song bounds (Sect. 6.2.3).** `tildeLaw D j` is the law of
--   $\tilde D_j = D_1 + \dots + D_j$, the lead-time demand of the single-stage system with lead
--   time $L_1 + \dots + L_j$, as an iterated convolution. `nvCostOf a b μ y` is the newsvendor
--   cost $\mathbb{E}[a(y - D)^+ + b(D - y)^+]$ under the law $\mu$. `pipelineMean D j` is
--   $\mathbb{E}[D_1] + \dots + \mathbb{E}[D_{j-1}]$, the expected stock in transit to stages
--   $1, \dots, j-1$. `ssLower N h p D j` is $g^l_j$, the truncated cost (6.31) with every local
--   holding cost replaced by $h_j$: since all stock is then held at stage 1, it is the
--   single-stage newsvendor cost with holding cost $h_j$, stockout cost $p + h'_{j+1}$ and
--   demand $\tilde D_j$, plus the holding cost $h_j$ of the pipeline stock; `ssUpper N h p D j`
--   is $g^u_j$, the same with holding cost $\sum_{k=1}^j h_k$.
--
--   **Guaranteed-service serial systems (Sect. 6.3.4).** With committed service times $S_i$,
--   `gsInbound N SIN S i` is the inbound time $SI_i = S_{i+1}$ ($SI_N$ external), `gsCost` is the
--   expected holding cost (6.37), $g(S) = \sum_i h_i k \sqrt{SI_i + T_i - S_i}$ with
--   $k = z_\alpha \sigma$, and `GSFeasible` is (6.39)-(6.42) without integrality: every $S_i$ and
--   every net lead time $SI_i + T_i - S_i$ is nonnegative.
--
--   **Formalization Note** Stages are indexed by natural numbers $1, \dots, N$; values of the
--   parameter functions outside that range are never used. The recursion is defined for every
--   $S$ so that the cost of an arbitrary base-stock vector is a value of the same functions, as
--   the book notes after Theorem 6.3. All expectations are Lebesgue integrals and the theorems
--   assume finite means, under which every integrand is integrable.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, Sect. 6.2.1 pp. 191-193 (Eq. 6.1, 6.4, Table 6.1), Sect. 6.2.2 pp. 194-196 (Eq. 6.21-6.27), Sect. 6.2.3 pp. 200-201 (Eq. 6.31, the functions gl_j, gu_j), Sect. 6.3.4 pp. 207-208 (Eq. 6.37-6.42)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-! ### Echelon accounting, Sect. 6.2.1 -/

/-- Table 6.1: the local holding cost `h'ⱼ = ∑_{i=j}^N hᵢ` recovered from echelon costs. -/
def localHolding (N : ℕ) (h : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.Icc j N, h i

/-- (6.4): the echelon holding cost `hⱼ = h'ⱼ − h'ⱼ₊₁`, with `h'_{N+1} = 0`. -/
def echelonHolding (N : ℕ) (h' : ℕ → ℝ) (j : ℕ) : ℝ :=
  h' j - (if j < N then h' (j + 1) else 0)

/-- (6.1): stage `j`'s echelon on-hand inventory `Iⱼ = ∑_{i=1}^j (I'ᵢ + ITᵢ₋₁)`, `IT₀ = 0`. -/
def echelonOnHand (I' IT : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 j, (I' i + if i = 1 then 0 else IT (i - 1))

/-! ### The Clark-Scarf recursion, Sect. 6.2.2 -/

/-- `ḡⱼ(x | S)` of (6.21)-(6.23), parametrised by the echelon base-stock vector `S`:
`ḡ₀(x) = (p + h'₁) x⁻` and `ḡⱼ₊₁(x) = gⱼ₊₁(min{Sⱼ₊₁, x})` with
`gⱼ₊₁(y) = E[hⱼ₊₁ (y − Dⱼ₊₁) + ḡⱼ(y − Dⱼ₊₁)]`. -/
noncomputable def csBar (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) :
    ℕ → ℝ → ℝ
  | 0 => fun x => (p + localHolding N h 1) * max (-x) 0
  | j + 1 => fun x =>
      ∫ d, (h (j + 1) * (min (S (j + 1)) x - d) + csBar N h p D S j (min (S (j + 1)) x - d))
        ∂(D (j + 1))

/-- (6.21): `ĝⱼ(x | S) = hⱼ x + ḡⱼ₋₁(x | S)`. -/
noncomputable def csHat (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (j : ℕ)
    (x : ℝ) : ℝ :=
  h j * x + csBar N h p D S (j - 1) x

/-- (6.22): `gⱼ(y | S) = E[ĝⱼ(y − Dⱼ | S)]`; the system cost of `S` is `g_N(S_N | S)`. -/
noncomputable def csG (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) (j : ℕ)
    (y : ℝ) : ℝ :=
  ∫ d, csHat N h p D S j (y - d) ∂(D j)

/-- (6.26): `S` is sequentially optimal when each `Sⱼ` minimises `gⱼ(· | S)`, which depends
only on `S₁, …, Sⱼ₋₁`. -/
def CSSequential (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (S : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 N, ∀ y, csG N h p D S j (S j) ≤ csG N h p D S j y

/-! ### The Shang-Song bounds, Sect. 6.2.3 -/

/-- The lead-time demand `D̃ⱼ = D₁ + ⋯ + Dⱼ` of the single-stage system with lead time
`L₁ + ⋯ + Lⱼ`, as the convolution of the stage laws. -/
noncomputable def tildeLaw (D : ℕ → Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | j + 1 => (tildeLaw D j).conv (D (j + 1))

/-- The single-stage newsvendor cost with holding cost `a`, stockout cost `b`, demand law `μ`. -/
noncomputable def nvCostOf (a b : ℝ) (μ : Measure ℝ) (y : ℝ) : ℝ :=
  ∫ d, (a * max (y - d) 0 + b * max (d - y) 0) ∂μ

/-- The expected pipeline stock of the `j`-stage truncated system, `E[D₁] + ⋯ + E[Dⱼ₋₁]`: the
stock in transit to stages `1, …, j − 1`, on which (6.31) charges holding cost. -/
noncomputable def pipelineMean (D : ℕ → Measure ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 j, ∫ d, d ∂(D i)

/-- `gˡⱼ`: (6.31) with every local holding cost replaced by `hⱼ`, when all stock is held at
stage 1: the single-stage newsvendor cost for `D̃ⱼ` plus the pipeline holding cost. -/
noncomputable def ssLower (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (j : ℕ) (y : ℝ) :
    ℝ :=
  nvCostOf (h j) (p + localHolding N h (j + 1)) (tildeLaw D j) y + h j * pipelineMean D j

/-- `gᵘⱼ`: (6.31) with every local holding cost replaced by `∑_{k=1}^j hₖ`. -/
noncomputable def ssUpper (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → Measure ℝ) (j : ℕ) (y : ℝ) :
    ℝ :=
  nvCostOf (∑ k ∈ Finset.Icc 1 j, h k) (p + localHolding N h (j + 1)) (tildeLaw D j) y
    + (∑ k ∈ Finset.Icc 1 j, h k) * pipelineMean D j

/-! ### Guaranteed-service serial systems, Sect. 6.3.4 -/

/-- The inbound committed service time `SIᵢ`: `Sᵢ₊₁` for `i < N`, the external `SI_N` at `N`. -/
def gsInbound (N : ℕ) (SIN : ℝ) (S : ℕ → ℝ) (i : ℕ) : ℝ := if i < N then S (i + 1) else SIN

/-- (6.37): the expected holding cost `g(S) = ∑ᵢ hᵢ k √(SIᵢ + Tᵢ − Sᵢ)` with `k = z_α σ`. -/
noncomputable def gsCost (N : ℕ) (h : ℕ → ℝ) (k : ℝ) (T : ℕ → ℝ) (SIN : ℝ) (S : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, h i * k * Real.sqrt (gsInbound N SIN S i + T i - S i)

/-- (6.39)-(6.42) without integrality: every CST and every net lead time is nonnegative. -/
def GSFeasible (N : ℕ) (T : ℕ → ℝ) (SIN : ℝ) (S : ℕ → ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 N, 0 ≤ S i) ∧ (∀ i ∈ Finset.Icc 1 N, S i ≤ gsInbound N SIN S i + T i)

end SupplyChainTheory


