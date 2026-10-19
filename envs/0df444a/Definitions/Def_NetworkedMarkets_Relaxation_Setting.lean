-- Prove2me | Definitions.Def_NetworkedMarkets_Relaxation_Setting
-- name    : NetworkedMarkets_Relaxation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:18.868462+00:00
-- url     : https://prove2.me/theorems/1805d778-4804-4234-b9ab-bcdbb709c8d5
-- title:
--   §2–§3.1 — networked market with type-specific fees: Assumptions 1–2, Γ × U, equilibrium (2a)–(2d), revenue problem (3), relaxation (7), system (8), special dual (EC.3)
-- statement:
--   This file sets up the model of Birge, Candogan, Chen and Saban for a platform that intermediates trade in a networked market and charges type-specific commissions and subscription fees.
--
--   **Value distributions.** A value distribution is a function $F:\mathbb R\to\mathbb R$ with an upper end of support $\bar v\in\mathbb R_+\cup\{\infty\}$. It satisfies **Assumption 1** (with the domain extension of p. 8) when $\bar v>0$; $0\le F\le 1$; $F(v)=0$ for $v\le 0$ and $F(v)=1$ for $v\ge\bar v$; $F$ is monotone, continuous (nonatomic) and tends to $1$ at $+\infty$; $F$ is continuously differentiable and strictly increasing on $(0,\bar v)$; and the mean is bounded, $\int_0^{\infty}(1-F(v))\,dv<\infty$. The inverse of (1) is defined from $F$ as
--   $$F^{-1}(u)=\inf\{v\ge 0:\ F(v)\ge u\},$$
--   which under Assumption 1 inverts $F$ on $[0,1)$ and gives $F^{-1}(1)=\bar v$ when $\bar v<\infty$.
--
--   **Market.** There are finitely many seller types $\mathcal S$ and buyer types $\mathcal B$, a compatibility network $E\subseteq\mathcal S\times\mathcal B$, seller masses $s_i$, buyer masses $b_j$, buyer disutilities $c_i$ from trading with type-$i$ sellers, and value distributions $F_{s_i}$, $F_{b_j}$. The **standing assumptions** of §2 are $s_i>0$, $b_j>0$, $c_i\ge 0$, every type has degree at least one in $E$, and every distribution satisfies Assumption 1. **Assumption 2** (p. 12) requires $u\mapsto uF^{-1}_{b_j}(1-u)$ to be strictly concave on $[0,1]$ and $u\mapsto -uF^{-1}_{s_i}(u)$ to be strictly concave on $[0,1]$ (on $[0,1)$ when $\bar v_{s_i}=\infty$).
--
--   **Fees and equilibrium.** The platform chooses commissions $\gamma=(\gamma^s,\gamma^b)$ and subscriptions $\mu=(\mu^s,\mu^b)$ in $\Gamma\times\mathcal U$: $\gamma^s_i\in[0,1]$, $\gamma^b_j\ge 0$, $\mu^s_i,\mu^b_j\ge 0$. A **competitive equilibrium** (Definition 1) is a tuple $(p,x,q^s,q^b)$ with $p\ge 0$ and
--   $$q^s_i=s_iF_{s_i}\big((1-\gamma^s_i)p_i-\mu^s_i\big),\qquad q^b_j=b_j\Big[1-F_{b_j}\Big(\min_{i':(i',j)\in E}\{(1+\gamma^b_j)p_{i'}+c_{i'}\}+\mu^b_j\Big)\Big],$$
--   the market-clearing conditions $q^s_i=\sum_{j:(i,j)\in E}x_{ij}$, $q^b_j=\sum_{i:(i,j)\in E}x_{ij}$, and $x_{ij}\ge 0$ on $E$ with $x_{ij}=0$ whenever seller type $i$ does not minimize $(1+\gamma^b_j)p_{i'}+c_{i'}$ among the sellers compatible with $j$.
--
--   **The revenue problem (3)** maximizes the platform revenue
--   $$\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p_ix_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)x_{ij}$$
--   over $(\gamma,\mu)\in\Gamma\times\mathcal U$ and competitive equilibria under $(\gamma,\mu)$; $V_{opt}$ is its maximum. A pair $(\gamma,\mu)$ is **optimal** when some equilibrium under it attains this maximum.
--
--   **The relaxation (7)** maximizes
--   $$h(q^s,q^b)=\sum_{j\in\mathcal B}F^{-1}_{b_j}\Big(1-\frac{q^b_j}{b_j}\Big)q^b_j-\sum_{i\in\mathcal S}F^{-1}_{s_i}\Big(\frac{q^s_i}{s_i}\Big)q^s_i-\sum_{i\in\mathcal S}c_iq^s_i$$
--   subject to the flow constraints (7b)–(7c), $q^b_j\le b_j$, $q^s_i\le s_i$ and $x_{ij}\ge 0$ on $E$; we write $g_j(q)=F^{-1}_{b_j}(1-q/b_j)q$ and $h_i(q)=F^{-1}_{s_i}(q/s_i)q$.
--
--   **System (8).** With $\tilde\gamma^s_i=1/(1-\gamma^s_i)$, $\tilde\mu^s_i=\mu^s_i/(1-\gamma^s_i)$, $\tilde\gamma^b_j=1/(1+\gamma^b_j)$, $\tilde\mu^b_j=\mu^b_j/(1+\gamma^b_j)$, the system (8a)–(8f) of Theorem 1(ii) in a price vector $p$ for a flow $x$ and a supply-demand vector $(\bar q^s,\bar q^b)$ is transcribed literally, with (8c)–(8d) over the edges of $E$.
--
--   **Special dual (EC.3).** For an optimal solution $(x,q^s,q^b)$ of (7), a special dual multiplier vector $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$ satisfies $g'_j(q^b_j)-\theta^b_j-\eta^b_j=0$, $h'_i(q^s_i)-\theta^s_i+\eta^s_i=0$, $\theta^b_j-\theta^s_i+\pi_{ij}-c_i=0$ on $E$, the complementarity conditions $q^b_j\le b_j\perp\eta^b_j\ge0$, $q^s_i\le s_i\perp\eta^s_i\ge0$, $x_{ij}\ge0\perp\pi_{ij}\ge0$, and the flow equations. The subscription-only fees (EC.104) are $\gamma=0$, $\mu^s_i=\theta^s_i-F^{-1}_{s_i}(\bar q^s_i/s_i)$, $\mu^b_j=F^{-1}_{b_j}(1-\bar q^b_j/b_j)-\theta^b_j$.
--
--   These objects are shared by every statement of the mission: Proposition 1, Corollary 1, the revenue bound (6), Lemma EC.1(ii), Proposition EC.1 at problem (7), the construction of Step (i-2) and Theorem 1.
--
--   **Formalization Note.** Types are arbitrary finite types; flows are functions $x:\mathcal S\to\mathcal B\to\mathbb R$ whose values off $E$ are never read (every flow sum ranges over $E$). $\bar v$ lives in `WithTop ℝ`. When $\bar v=\infty$, $F^{-1}(1)$ is the junk value $0$; buyer terms are unaffected because $0\cdot F^{-1}(1)=0$ is footnote 4's convention, and seller terms never meet it because the feasible set of (7) adds $q^s_i<s_i$ for such sellers and Assumption 2 is posed on $[0,1)$ for them (the paper's objective is $-\infty$ at $q^s_i=s_i$). The minimum in (2b) is expressed by `IsLeast` over the compatible sellers' costs, and "not in the argmin" in (2d) as "some compatible seller is strictly cheaper". The revenue of (3) is the fee-weighted sum (3a), not $h$. Derivatives $g'_j(q)$, $h'_i(q)$ in (EC.3) are limits of the derivative from inside $(0,b_j)$, $(0,s_i)$ (footnote 22's convention at the endpoints); requiring the limit to be a real number encodes their finiteness. `Standing1` collects the assumptions of §2, `Standing` adds Assumption 2.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), pp. 7–13, Assumption 1, (1), Definition 1, (2a)–(2d), (3a)–(3c), (6), Assumption 2, (7a)–(7f), Theorem 1 (8a)–(8f); pp. ec2–ec3 (PDF 46–47), (EC.1), footnote 22, Proposition EC.1(iii) (EC.3a)–(EC.3h); p. ec40 (PDF 84), (EC.104a)–(EC.104b)

import Mathlib

open Filter Topology MeasureTheory

namespace NetworkedMarkets.Relaxation

/-- A value distribution of one agent type (§2, p. 7): the cumulative distribution function `F`,
extended to all of `ℝ` as on p. 8, and the upper end `vbar ∈ ℝ₊ ∪ {∞}` of its support. -/
structure ValueDist where
  /-- the cumulative distribution function, extended to `ℝ` -/
  F : ℝ → ℝ
  /-- the upper end `v̄` of the support (`⊤` encodes `v̄ = ∞`) -/
  vbar : WithTop ℝ

namespace ValueDist

/-- The open interval `(0, v̄)`. -/
def Interior (D : ValueDist) : Set ℝ := {v | 0 < v ∧ (v : WithTop ℝ) < D.vbar}

/-- Assumption 1 (p. 8) together with the domain extension of p. 8: `F` is a nonatomic
(continuous) CDF on `[0, v̄]`, equal to `0` on `(-∞, 0]` and to `1` on `[v̄, ∞)`, continuously
differentiable and strictly increasing on `(0, v̄)`, with bounded mean `∫₀^{v̄} (1 - F) < ∞`. -/
def Assumption1 (D : ValueDist) : Prop :=
  0 < D.vbar ∧
  (∀ v : ℝ, 0 ≤ D.F v ∧ D.F v ≤ 1) ∧
  (∀ v : ℝ, v ≤ 0 → D.F v = 0) ∧
  (∀ v : ℝ, D.vbar ≤ (v : WithTop ℝ) → D.F v = 1) ∧
  Monotone D.F ∧
  Continuous D.F ∧
  Tendsto D.F atTop (𝓝 1) ∧
  StrictMonoOn D.F D.Interior ∧
  ContDiffOn ℝ 1 D.F D.Interior ∧
  IntegrableOn (fun v => 1 - D.F v) (Set.Ioi 0)

/-- The inverse `F⁻¹ : [0,1] → [0, v̄]` of (1), defined from `F` as the generalized inverse
`F⁻¹(u) = inf {v ≥ 0 : F(v) ≥ u}`. Under Assumption 1 it satisfies `F⁻¹(F(x)) = x` on `[0, v̄]`
and `F(F⁻¹(u)) = u` on `[0, 1)`; `F⁻¹(1) = v̄` when `v̄ < ∞`. When `v̄ = ∞`, `F⁻¹(1)` is the
junk value `0` (the infimum of the empty set). -/
noncomputable def Finv (D : ValueDist) (u : ℝ) : ℝ :=
  sInf {v : ℝ | 0 ≤ v ∧ u ≤ D.F v}

/-- The domain of the seller-side function `-u F⁻¹(u)` in Assumption 2: `[0, 1]` when `v̄ < ∞`,
and `[0, 1)` when `v̄ = ∞` (where `F⁻¹(1) = ∞`). -/
def sellerUnitDom (D : ValueDist) : Set ℝ := {u | 0 ≤ u ∧ u ≤ 1 ∧ (D.vbar = ⊤ → u < 1)}

end ValueDist

/-- A networked market (§2, p. 7): seller types `S`, buyer types `B`, the compatibility network
`E ⊆ S × B` (a pair `(i, j)` is seller type `i`, buyer type `j`), seller masses `s`, buyer masses
`b`, buyers' disutilities `c` from trading with each seller type, and the value distributions
`F_{s_i}`, `F_{b_j}`. -/
structure Market (S B : Type*) where
  E : Finset (S × B)
  s : S → ℝ
  b : B → ℝ
  c : S → ℝ
  Fs : S → ValueDist
  Fb : B → ValueDist

/-- Commission rates `γ = (γˢ, γᵇ)` and subscription fees `μ = (μˢ, μᵇ)` (p. 8). -/
structure Fees (S B : Type*) where
  γs : S → ℝ
  γb : B → ℝ
  μs : S → ℝ
  μb : B → ℝ

namespace Fees

variable {S B : Type*}

/-- The set `Γ × U` of feasible commission-subscription pairs (p. 8). -/
def InGammaU (f : Fees S B) : Prop :=
  (∀ i, 0 ≤ f.γs i ∧ f.γs i ≤ 1) ∧ (∀ j, 0 ≤ f.γb j) ∧ (∀ i, 0 ≤ f.μs i) ∧ (∀ j, 0 ≤ f.μb j)

/-- Transformed seller commission `γ̃ˢ_i = 1/(1 - γˢ_i)` (Theorem 1(ii)). -/
noncomputable def γts (f : Fees S B) (i : S) : ℝ := 1 / (1 - f.γs i)

/-- Transformed seller subscription `μ̃ˢ_i = μˢ_i/(1 - γˢ_i)`. -/
noncomputable def μts (f : Fees S B) (i : S) : ℝ := f.μs i / (1 - f.γs i)

/-- Transformed buyer commission `γ̃ᵇ_j = 1/(1 + γᵇ_j)`. -/
noncomputable def γtb (f : Fees S B) (j : B) : ℝ := 1 / (1 + f.γb j)

/-- Transformed buyer subscription `μ̃ᵇ_j = μᵇ_j/(1 + γᵇ_j)`. -/
noncomputable def μtb (f : Fees S B) (j : B) : ℝ := f.μb j / (1 + f.γb j)

end Fees

namespace Market

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- The buyer types compatible with seller type `i`. -/
def nbrS (M : Market S B) (i : S) : Finset B := Finset.univ.filter (fun j => (i, j) ∈ M.E)

/-- The seller types compatible with buyer type `j`. -/
def nbrB (M : Market S B) (j : B) : Finset S := Finset.univ.filter (fun i => (i, j) ∈ M.E)

/-- The standing assumptions of §2 (pp. 7–8): positive masses, nonnegative disutilities, every
type has degree at least one in `E`, and every value distribution satisfies Assumption 1. -/
def Standing1 (M : Market S B) : Prop :=
  (∀ i, 0 < M.s i) ∧ (∀ j, 0 < M.b j) ∧ (∀ i, 0 ≤ M.c i) ∧
  (∀ i, (M.nbrS i).Nonempty) ∧ (∀ j, (M.nbrB j).Nonempty) ∧
  (∀ i, (M.Fs i).Assumption1) ∧ (∀ j, (M.Fb j).Assumption1)

/-- Assumption 2 (p. 12): `u F⁻¹_{b_j}(1 - u)` is strictly concave on `[0, 1]` and `-u F⁻¹_{s_i}(u)`
is strictly concave on `[0, 1]` (on `[0, 1)` when `v̄_{s_i} = ∞`). -/
def Assumption2 (M : Market S B) : Prop :=
  (∀ j, StrictConcaveOn ℝ (Set.Icc 0 1) (fun u => u * (M.Fb j).Finv (1 - u))) ∧
  (∀ i, StrictConcaveOn ℝ (M.Fs i).sellerUnitDom (fun u => -(u * (M.Fs i).Finv u)))

/-- The standing assumptions from §3.1 on: those of §2 and Assumption 2. -/
def Standing (M : Market S B) : Prop := M.Standing1 ∧ M.Assumption2

/-- The effective cost `(1 + γᵇ_j) p_i + c_i` to a type-`j` buyer of buying from type-`i` sellers. -/
def cost (M : Market S B) (f : Fees S B) (p : S → ℝ) (i : S) (j : B) : ℝ :=
  (1 + f.γb j) * p i + M.c i

/-- The costs `{(1 + γᵇ_j) p_{i'} + c_{i'} : (i', j) ∈ E}` available to buyer type `j`. -/
def costSet (M : Market S B) (f : Fees S B) (p : S → ℝ) (j : B) : Set ℝ :=
  {v | ∃ i, (i, j) ∈ M.E ∧ v = M.cost f p i j}

/-- Definition 1 (p. 9): `(p, x, qˢ, qᵇ)` is a competitive equilibrium under `(γ, μ)`, i.e.
`p ≥ 0` and conditions (2a)–(2d) hold. -/
def IsCE (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ)
    (qb : B → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
  -- (2a)
  (∀ i, qs i = M.s i * (M.Fs i).F ((1 - f.γs i) * p i - f.μs i)) ∧
  -- (2b)
  (∀ j, ∃ m, IsLeast (M.costSet f p j) m ∧ qb j = M.b j * (1 - (M.Fb j).F (m + f.μb j))) ∧
  -- (2c)
  (∀ i, qs i = ∑ j ∈ M.nbrS i, x i j) ∧
  (∀ j, qb j = ∑ i ∈ M.nbrB j, x i j) ∧
  -- (2d)
  (∀ i j, (i, j) ∈ M.E → 0 ≤ x i j) ∧
  (∀ i j, (i, j) ∈ M.E → (∃ i', (i', j) ∈ M.E ∧ M.cost f p i' j < M.cost f p i j) → x i j = 0)

/-- The platform's revenue (3a): `Σ_{(i,j) ∈ E} (γˢ_i + γᵇ_j) p_i x_ij + Σ_{(i,j) ∈ E} (μˢ_i + μᵇ_j) x_ij`. -/
def rev (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) : ℝ :=
  ∑ e ∈ M.E, ((f.γs e.1 + f.γb e.2) * p e.1 * x e.1 e.2 + (f.μs e.1 + f.μb e.2) * x e.1 e.2)

/-- Feasibility in the revenue problem (3): constraints (3b)–(3c). -/
def Feas3 (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ)
    (qb : B → ℝ) : Prop :=
  f.InGammaU ∧ M.IsCE f p x qs qb

/-- The set of objective values of feasible solutions of (3); `V_opt` is its maximum. -/
def Value3 (M : Market S B) : Set ℝ :=
  {v | ∃ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
    M.Feas3 f p x qs qb ∧ v = M.rev f p x}

/-- `(γ, μ)` is an optimal commission-subscription pair: some competitive equilibrium under
`(γ, μ)` attains the maximum `V_opt` of (3) (p. 11). -/
def IsOptimalFees (M : Market S B) (f : Fees S B) : Prop :=
  ∃ (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
    M.Feas3 f p x qs qb ∧ IsGreatest M.Value3 (M.rev f p x)

/-- The buyer-side term `g_j(q) = F⁻¹_{b_j}(1 - q/b_j) q`. -/
noncomputable def gB (M : Market S B) (j : B) (q : ℝ) : ℝ :=
  (M.Fb j).Finv (1 - q / M.b j) * q

/-- The seller-side term `h_i(q) = F⁻¹_{s_i}(q/s_i) q`. -/
noncomputable def hS (M : Market S B) (i : S) (q : ℝ) : ℝ :=
  (M.Fs i).Finv (q / M.s i) * q

/-- The revenue upper bound (6), objective (7a):
`h(qˢ, qᵇ) = Σ_j F⁻¹_{b_j}(1 - qᵇ_j/b_j) qᵇ_j - Σ_i F⁻¹_{s_i}(qˢ_i/s_i) qˢ_i - Σ_i c_i qˢ_i`. -/
noncomputable def h (M : Market S B) (qs : S → ℝ) (qb : B → ℝ) : ℝ :=
  ∑ j, M.gB j (qb j) - ∑ i, M.hS i (qs i) - ∑ i, M.c i * qs i

/-- Feasibility in the relaxation (7): constraints (7b)–(7f), plus `qˢ_i < s_i` for seller types
with unbounded support (where the objective (7a) is `-∞` at `qˢ_i = s_i`). -/
def Feas7 (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) : Prop :=
  (∀ j, ∑ i ∈ M.nbrB j, x i j - qb j = 0) ∧
  (∀ i, qs i - ∑ j ∈ M.nbrS i, x i j = 0) ∧
  (∀ j, qb j ≤ M.b j) ∧
  (∀ i, qs i ≤ M.s i) ∧
  (∀ i j, (i, j) ∈ M.E → 0 ≤ x i j) ∧
  (∀ i, (M.Fs i).vbar = ⊤ → qs i < M.s i)

/-- `(x, qˢ, qᵇ)` is an optimal solution of (7). -/
def IsOpt7 (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) : Prop :=
  M.Feas7 x qs qb ∧
    ∀ (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ), M.Feas7 x' qs' qb' → M.h qs' qb' ≤ M.h qs qb

/-- The system (8a)–(8f) of Theorem 1(ii) in the price vector `p`, for the flow `x` and the
supply-demand vector `(q̄ˢ, q̄ᵇ)`; (8c)–(8d) range over the edges `(i, j) ∈ E`. -/
noncomputable def Sys8 (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ)
    (qs : S → ℝ) (qb : B → ℝ) : Prop :=
  -- (8a)
  (∀ i, 0 < qs i → p i - f.μts i - (M.Fs i).Finv (qs i / M.s i) * f.γts i = 0) ∧
  -- (8b)
  (∀ i, qs i = 0 → p i - f.μts i ≤ 0) ∧
  -- (8c)
  (∀ i j, (i, j) ∈ M.E → 0 < x i j →
    p i + f.μtb j + M.c i * f.γtb j - (M.Fb j).Finv (1 - qb j / M.b j) * f.γtb j = 0) ∧
  -- (8d)
  (∀ i j, (i, j) ∈ M.E → x i j = 0 →
    p i + f.μtb j + M.c i * f.γtb j - (M.Fb j).Finv (1 - qb j / M.b j) * f.γtb j ≥ 0) ∧
  -- (8e)
  (∀ i, f.γts i ≥ 1 ∧ f.μts i ≥ 0 ∧ p i ≥ 0) ∧
  -- (8f)
  (∀ j, f.γtb j ≥ 0 ∧ f.γtb j ≤ 1 ∧ f.μtb j ≥ 0)

/-- A special dual multiplier vector `(θᵇ, θˢ, ηᵇ, ηˢ, π)` for the optimal solution `(x, qˢ, qᵇ)` of
(7): conditions (EC.3a)–(EC.3h) of Proposition EC.1(iii) at the instance of Lemma EC.1(ii)
(`g_j = gB j`, `h_i = hS i`, `w_ij = c_i`). The slope `g'_j(q)` is the limit of the derivative
of `g_j` as the argument tends to `q` inside `(0, b_j)` (footnote 22); stating that this limit is the
real number `θᵇ_j + ηᵇ_j` includes the finiteness of `g'_j(qᵇ_j)`. Likewise for `h'_i`. -/
def IsSpecialDual (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ) : Prop :=
  -- (EC.3a): g'_j(qᵇ_j) - θᵇ_j - ηᵇ_j = 0
  (∀ j, Tendsto (deriv (M.gB j)) (𝓝[Set.Ioo 0 (M.b j)] (qb j)) (𝓝 (θb j + ηb j))) ∧
  -- (EC.3b): h'_i(qˢ_i) - θˢ_i + ηˢ_i = 0
  (∀ i, Tendsto (deriv (M.hS i)) (𝓝[Set.Ioo 0 (M.s i)] (qs i)) (𝓝 (θs i - ηs i))) ∧
  -- (EC.3c)
  (∀ i j, (i, j) ∈ M.E → θb j - θs i + π i j - M.c i = 0) ∧
  -- (EC.3d)
  (∀ j, qb j ≤ M.b j ∧ 0 ≤ ηb j ∧ ηb j * (M.b j - qb j) = 0) ∧
  -- (EC.3e)
  (∀ i, qs i ≤ M.s i ∧ 0 ≤ ηs i ∧ ηs i * (M.s i - qs i) = 0) ∧
  -- (EC.3f)
  (∀ i j, (i, j) ∈ M.E → 0 ≤ x i j ∧ 0 ≤ π i j ∧ π i j * x i j = 0) ∧
  -- (EC.3g)
  (∀ j, ∑ i ∈ M.nbrB j, x i j = qb j) ∧
  -- (EC.3h)
  (∀ i, ∑ j ∈ M.nbrS i, x i j = qs i)

/-- The subscription-only fees (EC.104) of the proof of Theorem 1, Step (i-2): `γ = 0`,
`μˢ_i = θˢ_i - F⁻¹_{s_i}(q̄ˢ_i/s_i)`, `μᵇ_j = F⁻¹_{b_j}(1 - q̄ᵇ_j/b_j) - θᵇ_j`. -/
noncomputable def subscriptionFees (M : Market S B) (qs : S → ℝ) (qb : B → ℝ) (θb : B → ℝ)
    (θs : S → ℝ) : Fees S B where
  γs := fun _ => 0
  γb := fun _ => 0
  μs := fun i => θs i - (M.Fs i).Finv (qs i / M.s i)
  μb := fun j => (M.Fb j).Finv (1 - qb j / M.b j) - θb j

end Market

end NetworkedMarkets.Relaxation


