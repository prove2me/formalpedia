-- Prove2me | Definitions.Def_TerracedZonal_Excess_Rings
-- name    : TerracedZonal_Excess_Rings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:30.204392+00:00
-- url     : https://prove2.me/theorems/90ed568e-2911-4c11-b44e-be7ccec0f57c
-- title:
--   Ring discretization, the window, and the terrace cost $G_\lambda$
-- statement:
--   Fix $N\ge3$. **Rings (eqs. (18)–(19)).** Let $\theta_{\mathrm{cap}}=\arccos(1-2/N)$, $h_0=\sqrt{2\pi\sqrt3/N}$ and $K=\max\big(1,\operatorname{round}((\pi-2\theta_{\mathrm{cap}})/h_0)\big)$. Rings $k=0,\dots,K-1$ run from north to south; the strip edges are $\vartheta_k=\theta_{\mathrm{cap}}+\tfrac kK(\pi-2\theta_{\mathrm{cap}})$, $\Delta z_k=\cos\vartheta_k-\cos\vartheta_{k+1}$, and the ideal populations and baselines are
--
--   $$y_k=(N-2)\frac{\Delta z_k}{\sum_{j=0}^{K-1}\Delta z_j},\qquad y_k^{\mathrm{base}}=\max\big(1,\operatorname{round}(y_k)\big).$$
--
--   **Window (eq. (4)).** With $w=\max(20,\operatorname{round}(0.65N^{1/3}))$, an integer population vector $m=(m_0,\dots,m_{K-1})$ lies in the window when $m_k\ge1$ and $|m_k-y_k^{\mathrm{base}}|\le w$ for every $k$.
--
--   **Costs (eqs. (5), (6), (30)).** For a population vector $m$ and $\lambda\in\mathbb R$,
--
--   $$\psi_{\mathrm{stretch}}(m,y)=c_{\mathrm{stretch}}\frac{(m-y)^2}{y^{1/3}m^{2/3}},\qquad S(m)=\sum_{1\le k<K,\ m_k\ne m_{k-1}}\tfrac12(y_{k-1}+y_k),$$
--
--   $$G_\lambda(m)=\sum_{k=0}^{K-1}\psi_{\mathrm{stretch}}(m_k,y_k)+\lambda S(m).$$
--
--   $\min G_\lambda$ denotes the minimum over all integer vectors with every $m_k\ge1$ (Lemma E.5), and $\min_{\Sigma}G_\lambda$ the minimum over those with $\sum_k m_k=N-2$ in addition.
--
--   **Formalization Note** `round` is Mathlib's rounding, half-integers up. The minima are infima (`⨅`) over subtypes; Lemma E.5 asserts that they are attained for large $N$. With no feasible vector (only possible for the constrained minimum when $K>N-2$) the infimum is $0$.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), eqs. (4)–(6) pp. 6–7 (PDF 7–8), eqs. (18)–(19) p. 19 (PDF 20), eq. (30) p. 29 (PDF 30), Lemma E.5 p. 30 (PDF 31)

import Definitions.Def_TerracedZonal_Excess_Constants

namespace TerracedZonal.Excess

open Real

/-- Polar-cap colatitude `θ_cap = arccos (1 - 2/N)`, eq. (18), p. 19 (PDF 20). -/
noncomputable def thetaCap (N : ℕ) : ℝ := Real.arccos (1 - 2 / (N : ℝ))

/-- Ring spacing `h₀ = √(2π√3 / N)`, eq. (18), p. 19 (PDF 20). -/
noncomputable def h0 (N : ℕ) : ℝ := Real.sqrt (2 * π * Real.sqrt 3 / (N : ℝ))

/-- Ring count `K = max(1, round((π - 2θ_cap)/h₀))`, eq. (18), p. 19 (PDF 20);
Mathlib's `round` rounds half-integers up. -/
noncomputable def ringCount (N : ℕ) : ℕ :=
  max 1 (round ((π - 2 * thetaCap N) / h0 N)).toNat

/-- A population vector: one natural number per ring `k = 0, …, K-1` (north to south). -/
abbrev Pops (N : ℕ) := Fin (ringCount N) → ℕ

/-- Strip edges `ϑ_k = θ_cap + (k/K)(π - 2θ_cap)`, `k = 0, …, K`, p. 19 (PDF 20). -/
noncomputable def stripEdge (N : ℕ) (k : ℕ) : ℝ :=
  thetaCap N + ((k : ℝ) / (ringCount N : ℝ)) * (π - 2 * thetaCap N)

/-- `Δz_k^{ideal} = cos ϑ_k - cos ϑ_{k+1}`, eq. (19), p. 19 (PDF 20). -/
noncomputable def deltaZ (N : ℕ) (k : ℕ) : ℝ := Real.cos (stripEdge N k) - Real.cos (stripEdge N (k + 1))

/-- Ideal real populations `y_k = (N - 2) Δz_k / ∑_{j<K} Δz_j`, eq. (19), p. 19 (PDF 20). -/
noncomputable def idealPop (N : ℕ) (k : Fin (ringCount N)) : ℝ :=
  ((N : ℝ) - 2) * deltaZ N k / ∑ j : Fin (ringCount N), deltaZ N j

/-- Rounded baseline `y_k^{base} = max(1, round(y_k))`, p. 19 (PDF 20). -/
noncomputable def basePop (N : ℕ) (k : Fin (ringCount N)) : ℕ :=
  max 1 (round (idealPop N k)).toNat

/-- Window half-width `w = max(20, round(0.65 N^{1/3}))`, eq. (4), p. 6 (PDF 7). -/
noncomputable def halfWidth (N : ℕ) : ℕ :=
  max 20 (round ((65 / 100 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ))).toNat

/-- The Stage-1 window, eq. (4), p. 6 (PDF 7): ring `k` takes one of the candidates
`m_{k,i} = y_k^{base} + (i - w)`, `i = 0, …, 2w`, i.e. `|m_k - y_k^{base}| ≤ w`,
candidates `< 1` excluded. -/
def InWindow (N : ℕ) (m : Pops N) : Prop :=
  ∀ k, 1 ≤ m k ∧ basePop N k ≤ m k + halfWidth N ∧ m k ≤ basePop N k + halfWidth N

/-- Node stretching cost `ψ_stretch(m, y) = c_stretch (m - y)² / (y^{1/3} m^{2/3})`, eq. (5),
p. 6 (PDF 7). Used at `m ≥ 1`, `y > 0`. -/
noncomputable def psiStretch (m y : ℝ) : ℝ :=
  cStretch * (m - y) ^ 2 / (y ^ (1 / 3 : ℝ) * m ^ (2 / 3 : ℝ))

/-- Total stretching cost `Ψ(m) = ∑_k ψ_stretch(m_k, y_k)`. -/
noncomputable def stretchCost (N : ℕ) (m : Pops N) : ℝ :=
  ∑ k, psiStretch (m k : ℝ) (idealPop N k)

/-- The previous ring `k - 1` of a ring `k ≥ 1`. -/
def prevRing {K : ℕ} (k : Fin K) (hk : 0 < k.val) : Fin K := ⟨k.val - 1, by omega⟩

/-- Seam weight `S(m) = ∑_{1 ≤ k < K, m_k ≠ m_{k-1}} ½ (y_{k-1} + y_k)`, eq. (30),
p. 29 (PDF 30) (the sum in (6) and in locality (A)). -/
noncomputable def seamSum (N : ℕ) (m : Pops N) : ℝ :=
  ∑ k : Fin (ringCount N),
    if hk : 0 < k.val then
      (if m k ≠ m (prevRing k hk) then (idealPop N (prevRing k hk) + idealPop N k) / 2 else 0)
    else 0

/-- `G_λ(m) = ∑_k ψ_stretch(m_k, y_k) + λ S(m)`, eq. (30), p. 29 (PDF 30). Stage 1 minimizes
`G_{c_step}`; it is defined here for every population vector. -/
noncomputable def Gcost (lam : ℝ) (N : ℕ) (m : Pops N) : ℝ := stretchCost N m + lam * seamSum N m

/-- `min_m G_λ(m)` over all integer population vectors with every `m_k ≥ 1` (no window), the
minimum of Lemma E.5, p. 30 (PDF 31). The index set is nonempty and `G_λ ≥ 0` for `λ ≥ 0`. -/
noncomputable def minG (lam : ℝ) (N : ℕ) : ℝ :=
  ⨅ m : {m : Pops N // ∀ k, 1 ≤ m k}, Gcost lam N m.1

/-- The same minimum under the mass constraint `∑_k m_k = N - 2` (written `∑ m_k + 2 = N`),
Lemma E.5, p. 30 (PDF 31). The index set is nonempty exactly when `K ≤ N - 2`. -/
noncomputable def minGMass (lam : ℝ) (N : ℕ) : ℝ :=
  ⨅ m : {m : Pops N // (∀ k, 1 ≤ m k) ∧ ∑ k, m k + 2 = N}, Gcost lam N m.1

end TerracedZonal.Excess


