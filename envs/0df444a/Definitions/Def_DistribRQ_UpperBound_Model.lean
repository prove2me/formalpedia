-- Prove2me | Definitions.Def_DistribRQ_UpperBound_Model
-- name    : DistribRQ_UpperBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:46.559761+00:00
-- url     : https://prove2.me/theorems/5da9c350-15bf-4a9e-8d2a-2ff95e634d89
-- title:
--   §3, (1)–(3), (5)–(7), Lemma 3, pp. 5–13, A1–A4 — OWMR primitives, single-stage (r,Q) costs, the bound Γ̄, Λ0, Ĉ0, C^U and the encoded system cost
-- statement:
--   This module sets up the one-warehouse, multi-retailer (OWMR) distribution system of Zhu, Chen, Hu and Yang under a modified echelon $(r,Q)$ policy, and every cost function used in their upper bound on the long-run average system cost.
--
--   **Primitives** (§3, p. 5). There are $N\ge1$ retailers. Retailer $i$ faces Poisson demand of rate $\lambda_i>0$, receives shipments after a constant lead time $L_i>0$, pays a fixed cost $K_i>0$ per shipment, an echelon holding cost rate $h_i>0$ and a backlog cost rate $p_i>0$. The warehouse has lead time $L_0>0$, fixed cost $K_0>0$ and echelon holding cost rate $h_0>0$. The system demand rate is $\lambda_0=\sum_{i=1}^N\lambda_i$, and $\bar K=\max_i K_i$ (p. 11). A **policy** is given by reorder levels $r_i, r_0$ and order quantities $Q_i>0$, $Q_0>0$.
--
--   **Single-stage costs** (p. 10). With $D_i\sim\mathrm{Poisson}(\lambda_iL_i)$ the lead-time demand of retailer $i$,
--   $$
--   G_i(y)=\mathbb E\big[h_i(y-D_i)^+ + (h_0+p_i)(y-D_i)^-\big],\qquad C_i(r_i,Q_i)=\frac{\lambda_iK_i+\int_{r_i}^{r_i+Q_i}G_i(y)\,dy}{Q_i}.
--   $$
--
--   **The envelope of Lemma 3** (pp. 11–12). Write $G_i(w_i)=\sup_{r_i<z\le r_i+Q_i}G_i(z)$, $M_j=\max\{G_j(w_j),C_j(r_j,Q_j)\}$ and $S_i=\sum_{j\ne i}(r_j+Q_j)$. For a warehouse echelon inventory level $x$,
--   $$
--   \bar\Gamma_i(x)=\sum_{j\ne i}M_j+\begin{cases}M_i & \text{if } x-S_i>r_i,\\ \max\{G_i(x-S_i),\,M_i\} & \text{otherwise,}\end{cases}\qquad \bar\Gamma(x)=\max_{1\le i\le N}\bar\Gamma_i(x).
--   $$
--
--   **Warehouse-level costs** (p. 12 and Theorem 1, p. 13). With $D_0\sim\mathrm{Poisson}(\lambda_0L_0)$,
--   $$
--   \hat G(y)=\bar\Gamma(y)-\sum_{i}C_i(r_i,Q_i),\quad \Lambda_0(y)=\mathbb E\big[h_0(y-D_0)+\hat G(y-D_0)\big],\quad \hat C_0(r_0,Q_0)=\frac{1}{Q_0}\Big[\lambda_0K_0+\int_{r_0}^{r_0+Q_0}\Lambda_0(y)\,dy\Big],
--   $$
--   and $C^U(r,Q)=\sum_iC_i(r_i,Q_i)+\hat C_0(r_0,Q_0)+\lambda_0\bar K/Q_0$.
--
--   **Feasible states and charges** (p. A1). A vector $z=(z_1,\dots,z_N)$ of retailer inventory positions is *feasible* at warehouse echelon level $x$ if $z_j\le r_j+Q_j$ for all $j$, the warehouse on-hand stock $x-\sum_jz_j$ is nonnegative, and, whenever that on-hand stock is positive, $z_i>r_i$ for every $i$. A family of charges $c_i:\mathbb R\to\mathbb R$ is *admissible* if $c_i(z)\le\max\{G_i(z),C_i(r_i,Q_i)\}$ for $z>r_i$ and $c_i(z)\le G_i(z)$ for $z\le r_i$; these are the cost-assessment schemes of §4.2.2 as the proof of Lemma 3 uses them. Given a Markov kernel $\kappa$ (the law of the retailer positions given the warehouse echelon level), the expected retailer charge is $\hat\Gamma(x)=\int\sum_ic_i(z_i)\,\kappa(x)(dz)$, and $\Gamma_0(y)=\mathbb E[h_0(y-D_0)]+\mathbb E[\hat\Gamma(y-D_0)]$ (App. A (9)).
--
--   **System cost** (1), p. 7. For a retailer cost-rate function $\Omega$,
--   $$
--   C(r,Q)=\frac{1}{Q_0}\Big[\lambda_0K_0+\int_{r_0}^{r_0+Q_0}\mathbb E\big[h_0(y-D_0)+\Omega(y)\big]\,dy\Big].
--   $$
--
--   These objects are the vocabulary of Theorem 1 and of the steps of its proof.
--
--   **Formalization Note** Retailer $i\in\{1,\dots,N\}$ is `i : Fin N` (shifted by one); the warehouse is separate data. $r_i,Q_i$ are real (the paper's continuous approximation, p. 7), with $Q_i>0$, $Q_0>0$. Poisson expectations are Bochner integrals over $\mathbb N$ against `poissonMeasure`, evaluated at real arguments $y-n$. $G_i(w_i)$ is the supremum of $G_i$ over $(r_i,r_i+Q_i]$, because the paper's $\arg\max$ need not be attained on the half-open interval. The admissible-charge condition uses "$\le$" where p. A1 has "$=$" in the case $z\le r_i$, which is more general.
-- source:
--   Zhu, Chen, Hu & Yang, A simple heuristic policy for stochastic distribution inventory systems with fixed shipment costs, SSRN 2921743 (2020-09-08 copy), pp. 5–13 and A1–A4: §3 (p. 5), (1) (p. 7), (2)–(3) (p. 10), K̄ and Lemma 3 (pp. 11–12), (5)–(7) (p. 12), Theorem 1 (p. 13), feasible states and charges (p. A1), App. A (9) (p. A4)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DistribRQ.UpperBound

/-- The primitives of the one-warehouse, `N`-retailer system of §3, p. 5 (Zhu, Chen, Hu & Yang,
SSRN 2921743). Retailer `i : Fin N` is the paper's Retailer `i + 1`; the warehouse (the paper's
Installation 0) is the separate data `L0`, `K0`, `h0`.

* `lam i` — Poisson demand rate `λᵢ` of retailer `i`;
* `L i`, `L0` — constant lead times `Lᵢ > 0`, `L₀ > 0`;
* `K i`, `K0` — fixed cost per shipment `Kᵢ`, `K₀` (positive, p. 2);
* `h i`, `h0` — echelon holding cost rates `hᵢ > 0`, `h₀ > 0`;
* `p i` — backlog cost rate `pᵢ > 0` of retailer `i`. -/
structure Primitives (N : ℕ) where
  lam : Fin N → ℝ
  L : Fin N → ℝ
  K : Fin N → ℝ
  h : Fin N → ℝ
  p : Fin N → ℝ
  L0 : ℝ
  K0 : ℝ
  h0 : ℝ
  lam_pos : ∀ i, 0 < lam i
  L_pos : ∀ i, 0 < L i
  K_pos : ∀ i, 0 < K i
  h_pos : ∀ i, 0 < h i
  p_pos : ∀ i, 0 < p i
  L0_pos : 0 < L0
  K0_pos : 0 < K0
  h0_pos : 0 < h0

/-- The parameters `(r, Q)` of a modified echelon `(r,Q)` policy (Definition 1, p. 6): reorder
levels `rᵢ`, `r₀` and order quantities `Qᵢ > 0`, `Q₀ > 0`. They are real numbers, as in the
continuous approximation of p. 7. -/
structure Policy (N : ℕ) where
  r : Fin N → ℝ
  Q : Fin N → ℝ
  r0 : ℝ
  Q0 : ℝ
  Q_pos : ∀ i, 0 < Q i
  Q0_pos : 0 < Q0

/-- Expectation `E[f(D)]` of `f` at a Poisson random variable `D` with mean `μ`. -/
noncomputable def EPois (μ : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∫ n, f n ∂(poissonMeasure μ.toNNReal)

variable {N : ℕ} (P : Primitives N) (π : Policy N)

/-- System demand rate `λ₀ = Σᵢ λᵢ` (p. 5). -/
noncomputable def lam0 : ℝ := ∑ i, P.lam i

/-- `K̄ = max_{i ∈ [N]⁺} Kᵢ` (p. 11). -/
noncomputable def Kbar [NeZero N] : ℝ := Finset.univ.sup' Finset.univ_nonempty P.K

/-- (2), p. 10: `Gᵢ(y) = E[hᵢ(y − Dᵢ)⁺ + (h₀ + pᵢ)(y − Dᵢ)⁻]`, with `Dᵢ ~ Poisson(λᵢLᵢ)` the
lead-time demand of retailer `i`. -/
noncomputable def G (i : Fin N) (y : ℝ) : ℝ :=
  EPois (P.lam i * P.L i)
    (fun n => P.h i * max (y - n) 0 + (P.h0 + P.p i) * max (-(y - n)) 0)

/-- (3), p. 10: `Cᵢ(rᵢ,Qᵢ) = (λᵢKᵢ + ∫_{rᵢ}^{rᵢ+Qᵢ} Gᵢ(y) dy) / Qᵢ`. -/
noncomputable def Ccost (i : Fin N) : ℝ :=
  (P.lam i * P.K i + ∫ y in π.r i..π.r i + π.Q i, G P i y) / π.Q i

/-- `Gᵢ(wᵢ)` of Lemma 3 (p. 12), read as the supremum of `Gᵢ` over `(rᵢ, rᵢ + Qᵢ]`. -/
noncomputable def Gw (i : Fin N) : ℝ :=
  sSup (G P i '' Set.Ioc (π.r i) (π.r i + π.Q i))

/-- `Σ_{j ≠ i} (rⱼ + Qⱼ)`. -/
noncomputable def S (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (π.r j + π.Q j)

/-- The own-retailer term of `Γ̄ᵢ` in Lemma 3 (p. 12), at warehouse echelon level `x = IL₀(t)`. -/
noncomputable def GammaBarOwn (i : Fin N) (x : ℝ) : ℝ :=
  if x - S π i > π.r i then max (Gw P π i) (Ccost P π i)
  else max (G P i (x - S π i)) (max (Gw P π i) (Ccost P π i))

/-- `Γ̄ᵢ(x)` of Lemma 3 (p. 12). -/
noncomputable def GammaBarI (i : Fin N) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, max (Gw P π j) (Ccost P π j) + GammaBarOwn P π i x

/-- `Γ̄(x) = max_{i ∈ [N]⁺} Γ̄ᵢ(x)`, (4) of Lemma 3 (p. 11). -/
noncomputable def GammaBar [NeZero N] (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => GammaBarI P π i x)

/-- (5), p. 12: `Ĝ(y) = Γ̄(y) − Σᵢ Cᵢ(rᵢ,Qᵢ)`. -/
noncomputable def Ghat [NeZero N] (y : ℝ) : ℝ :=
  GammaBar P π y - ∑ i, Ccost P π i

/-- (6), p. 12: `Λ₀(y) = E[h₀(y − D₀) + Ĝ(y − D₀)]`, `D₀ ~ Poisson(λ₀L₀)`. -/
noncomputable def Lambda0 [NeZero N] (y : ℝ) : ℝ :=
  EPois (lam0 P * P.L0) (fun n => P.h0 * (y - n) + Ghat P π (y - n))

/-- (7), p. 12: `Ĉ₀(r₀,Q₀) = (1/Q₀)[λ₀K₀ + ∫_{r₀}^{r₀+Q₀} Λ₀(y) dy]`. -/
noncomputable def C0hat [NeZero N] : ℝ :=
  (lam0 P * P.K0 + ∫ y in π.r0..π.r0 + π.Q0, Lambda0 P π y) / π.Q0

/-- Theorem 1, p. 13: `C^U(r,Q) = Σᵢ Cᵢ(rᵢ,Qᵢ) + Ĉ₀(r₀,Q₀) + λ₀K̄/Q₀`. -/
noncomputable def CU [NeZero N] : ℝ :=
  ∑ i, Ccost P π i + C0hat P π + lam0 P * Kbar P / π.Q0

/-- Feasible retailer inventory-position vectors `z = (IP₁(t), …, IP_N(t))` at warehouse
echelon level `IL₀(t) = x`, under the modified echelon `(r,Q)` policy (p. A1):
`IPⱼ ≤ rⱼ + Qⱼ`; the warehouse on-hand stock `OI₀⁺ = x − Σⱼ IPⱼ` is nonnegative; and
`OI₀⁺ > 0` forces `rᵢ < IPᵢ` for every retailer. -/
def Feasible (x : ℝ) : Set (Fin N → ℝ) :=
  {z | (∀ j, z j ≤ π.r j + π.Q j) ∧ ∑ j, z j ≤ x ∧ (∑ j, z j < x → ∀ i, π.r i < z i)}

/-- Charges `cᵢ(z)` (cost rate of retailer `i`, Type II fixed costs excluded, at inventory
position `z`) that follow the cost-assessment schemes of §4.2.2 as used on p. A1:
`cᵢ(z) ≤ max{Gᵢ(z), Cᵢ(rᵢ,Qᵢ)}` if `z > rᵢ`, and `cᵢ(z) ≤ Gᵢ(z)` if `z ≤ rᵢ`. -/
def AdmissibleCharge (c : Fin N → ℝ → ℝ) : Prop :=
  (∀ i z, π.r i < z → c i z ≤ max (G P i z) (Ccost P π i)) ∧
  (∀ i z, z ≤ π.r i → c i z ≤ G P i z)

/-- `Γ̂(x)`: the expected total retailer charge at warehouse echelon level `x`, when the vector
of retailer inventory positions has conditional law `κ x`. -/
noncomputable def GammaHat (κ : Kernel ℝ (Fin N → ℝ)) (c : Fin N → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, ∑ i, c i (z i) ∂(κ x)

/-- App. A (9), first line, p. A4: `Γ₀(y) = E[h₀(y − D₀)] + E[Γ̂(y − D₀)]`. -/
noncomputable def Gamma0 (κ : Kernel ℝ (Fin N → ℝ)) (c : Fin N → ℝ → ℝ) (y : ℝ) : ℝ :=
  EPois (lam0 P * P.L0) (fun n => P.h0 * (y - n)) +
    EPois (lam0 P * P.L0) (fun n => GammaHat κ c (y - n))

/-- (1), p. 7: the long-run average system cost
`C(r,Q) = (1/Q₀)[λ₀K₀ + ∫_{r₀}^{r₀+Q₀} E[h₀(y − D₀) + Ω(y)] dy]`, as a function of the
retailers' cost rate `Ω`. -/
noncomputable def Csys (Omega : ℝ → ℝ) : ℝ :=
  (lam0 P * P.K0 +
    ∫ y in π.r0..π.r0 + π.Q0, EPois (lam0 P * P.L0) (fun n => P.h0 * (y - n) + Omega y)) /
    π.Q0

end DistribRQ.UpperBound


