-- Prove2me | Definitions.Def_RAREPricing_Existence_Model
-- name    : RAREPricing_Existence_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:24:33.64013+00:00
-- url     : https://prove2.me/theorems/b1bc6f89-5717-4cf9-9dc5-7e2503f62bea
-- title:
--   Budget-constrained pricing market: demand sets, allocation rules, revenues, ν/β/κ, δ-additive κ-RARE (§3, §4.2, Definition 2)
-- statement:
--   A **market instance** $I=([n],[m],(u_i)_{i=1}^n,(b_i)_{i=1}^n)$ has $n\ge1$ buyers and $m\ge2$ divisible goods. Buyer $i$ has a budget $b_i>0$ and a utility $u_i:[0,1]^m\to\mathbb R$ with $u_i(0)=0$, continuous on the cube $[0,1]^m$ and **strictly monotone** there: for distinct $x,y\in[0,1]^m$ with $x_j\le y_j$ for all $j$, $u_i(x)<u_i(y)$. Write $B=\sum_i b_i$, $b_{\mathrm{avg}}=B/n$, $b_{\min}=\min_i b_i$.
--
--   For prices $p\in\mathbb R^m_{\ge0}$, buyer $i$'s **non-rivalrous demand** is the set of maximizers
--   $$\mathrm{Dem}_i(p)=\operatorname*{argmax}_{z\in[0,1]^m,\ p^\top z\le b_i} u_i(z),\qquad \mathrm{DemNR}(p)=\prod_{i=1}^n \mathrm{Dem}_i(p).$$
--   An allocation $x\in[0,1]^{n\times m}$ ($x_{i,j}$ = buyer $i$'s fraction of good $j$) **Pareto dominates** $y$ if $u_i(x_i)\ge u_i(y_i)$ for every $i$ and $u_i(x_i)>u_i(y_i)$ for some $i$; $\mathrm{PO}(S)$ is the set of $x\in S$ dominated by no $y\in S$. The **affordable rivalrous allocations** are $\mathrm{AffR}(p)=\{x\in[0,1]^{n\times m}:\sum_i x_{i,j}\le1\ \forall j,\ \sum_j p_jx_{i,j}\le b_i\ \forall i\}$ and the **rivalrous demand** is $\mathrm{DemR}(p)=\mathrm{PO}(\mathrm{AffR}(p))$. $\mathrm{Dem}$ denotes $\mathrm{DemR}$ or $\mathrm{DemNR}$ according to the setting.
--
--   The setting fixes $\nu,\beta$ and $\kappa:=B/(\nu\beta)$: rivalrous $\nu=1,\beta=B$ (so $\kappa=1$); non-rivalrous $\nu=n,\beta=b_{\min}$ (so $\kappa=b_{\mathrm{avg}}/b_{\min}$).
--
--   Seller $j$'s revenue is $R_j(p,x)=p_j\sum_i x_{i,j}$ and $R_{\mathrm{all}}(p,x)=\sum_jR_j(p,x)$. An **allocation rule** is a map $A$ with $A(p)\in\mathrm{Dem}(p)$ for every $p\ge0$; it is **continuous** if it is continuous on $\mathbb R^m_{\ge0}$. Write $R^A_j(p)=R_j(p,A(p))$ and $R_{\mathrm{all}}(p)=R_{\mathrm{all}}(p,A(p))$.
--
--   **Definition 2.** For $\delta,\kappa$, a price vector $p\in\mathbb R^m_{\ge0}$ is a **$\delta$-additive $\kappa$-RARE** for $A$ if for every seller $j$ and every deviation $q_j\ge0$ there is a response $q_{-j}\in\mathbb R^{[m]\setminus\{j\}}_{\ge0}$ such that, with $q=(q_j,q_{-j})$,
--   $$R^A_j(q)\le\kappa R^A_j(p)+\delta\quad\text{and}\quad R^A_k(q)\ge R^A_k((q_j,p_{-j}))\ \ \forall k\ne j .$$
--   A $\kappa$-RARE is the case $\delta=0$.
--
--   Also defined: the scaled simplex $\beta\Delta_m=\{x\in\mathbb R^m_{\ge0}:\sum_jx_j=\beta\}$; the union of upper faces $U=\{x\in\prod_j[\ell_j,h_j]: x_i=h_i\text{ for some }i\}$ of a box (Lemma 2); a **security pair** $(\rho_j,\sigma_j)$ of seller $j$ (the conclusion of Lemma 5: $\rho_j>0$, $\sigma_j\ge\rho_j/\nu$, and $R_j((\sigma_j,q_{-j}),x)\ge\rho_j$ for all $q_{-j}\ge0$, $x\in\mathrm{Dem}((\sigma_j,q_{-j}))$); and an **overpricing bound** $L_j$ (the conclusion of Lemma 6: $L_j\ge\max(B,\sigma_j)$ and $R_j(q,x)\le\rho_j/(2\kappa)$ whenever $q\ge0$, $x\in\mathrm{Dem}(q)$, $q_j>L_j$, $\max_{k\ne j}q_k=B$).
--
--   **Formalization Note.** Buyers and goods are `Fin n`, `Fin m`; prices are `Fin m → ℝ` with explicit nonnegativity; allocations are `Fin n → Fin m → ℝ`. Utilities are functions on `Fin m → ℝ` whose values off the cube are never used; strict monotonicity is `StrictMonoOn` for the Pi order. The response $(q_j,q_{-j})$ is `Function.update r j qj` (the $j$-th entry of `r` is ignored). An allocation rule is a total map on `Fin m → ℝ`; only its values at $p\ge0$ matter, and continuity is `ContinuousOn` the closed orthant. $\max_{k\ne j}q_k=B$ is written "all $q_k\le B$ for $k\ne j$, with equality for some $k\ne j$" (the index set is nonempty since $m\ge2$). `IsRARE A δ κ p` takes $\delta,\kappa$ as arguments; the constraints $\delta\ge0,\kappa\ge1$ are met by every instance used.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), pp. 12–14 (PDF 14–16) §3.1–3.4 and Definition 2; p. 15 (PDF 17) §4.2 table; p. 17 (PDF 19) Lemma 2; p. 20 (PDF 22) Lemmas 5–6

import Mathlib

namespace RAREPricing.Existence

/-- The unit cube `[0,1]^m` of bundles (Pi order on `Fin m → ℝ`). -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.Icc 0 1

/-- A market instance `I = ([n], [m], (u_i), (b_i))` (§3.1): `n ≥ 1` buyers, `m ≥ 2` goods,
budgets `b_i > 0`, utilities `u_i` on `[0,1]^m` with `u_i(0) = 0`, continuous and strictly
monotone on the cube. Values of `u i` outside the cube are never used. -/
structure Market (n m : ℕ) where
  u : Fin n → (Fin m → ℝ) → ℝ
  b : Fin n → ℝ
  one_le_n : 1 ≤ n
  two_le_m : 2 ≤ m
  b_pos : ∀ i, 0 < b i
  u_zero : ∀ i, u i 0 = 0
  u_continuousOn : ∀ i, ContinuousOn (u i) (cube m)
  u_strictMonoOn : ∀ i, StrictMonoOn (u i) (cube m)

namespace Market

variable {n m : ℕ}

/-- Total budget `B := ∑_i b_i`. -/
def totalBudget (M : Market n m) : ℝ := ∑ i, M.b i

/-- Average budget `b_avg := B / n`. -/
noncomputable def bavg (M : Market n m) : ℝ := M.totalBudget / n

/-- Minimum budget `b_min := min_i b_i` (the buyer set is nonempty since `n ≥ 1`). -/
noncomputable def bmin (M : Market n m) : ℝ :=
  Finset.univ.inf' ⟨⟨0, M.one_le_n⟩, Finset.mem_univ _⟩ M.b

end Market

variable {n m : ℕ}

/-- Buyer `i`'s budget set `{z ∈ [0,1]^m : pᵀz ≤ b_i}`. -/
def budgetSet (M : Market n m) (p : Fin m → ℝ) (i : Fin n) : Set (Fin m → ℝ) :=
  {z | z ∈ cube m ∧ ∑ j, p j * z j ≤ M.b i}

/-- Non-rivalrous demand of buyer `i`: `Dem_i(p) = argmax_{z ∈ [0,1]^m, pᵀz ≤ b_i} u_i(z)`. -/
def demandBuyer (M : Market n m) (p : Fin m → ℝ) (i : Fin n) : Set (Fin m → ℝ) :=
  {z | z ∈ budgetSet M p i ∧ ∀ z' ∈ budgetSet M p i, M.u i z' ≤ M.u i z}

/-- Combined non-rivalrous demand `DemNR(p) = ∏_i Dem_i(p)`; `x i j` is buyer `i`'s share of good `j`. -/
def DemNR (M : Market n m) (p : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {x | ∀ i, x i ∈ demandBuyer M p i}

/-- `x` Pareto dominates `y` (`x ≻ y`): no buyer is worse off and some buyer is strictly better off. -/
def ParetoDominates (M : Market n m) (x y : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, M.u i (y i) ≤ M.u i (x i)) ∧ ∃ i, M.u i (y i) < M.u i (x i)

/-- Pareto-optimal subset `PO(S) = {x ∈ S : no y ∈ S Pareto dominates x}`. -/
def PO (M : Market n m) (S : Set (Fin n → Fin m → ℝ)) : Set (Fin n → Fin m → ℝ) :=
  {x | x ∈ S ∧ ∀ y ∈ S, ¬ ParetoDominates M y x}

/-- Affordable rivalrous allocations `AffR(p)`: bundles in `[0,1]^m`, unit supply of each good,
and every buyer within budget. -/
def AffR (M : Market n m) (p : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  {x | (∀ i, x i ∈ cube m) ∧ (∀ j, ∑ i, x i j ≤ 1) ∧ ∀ i, ∑ j, p j * x i j ≤ M.b i}

/-- Rivalrous demand `DemR(p) = PO(AffR(p))`. -/
def DemR (M : Market n m) (p : Fin m → ℝ) : Set (Fin n → Fin m → ℝ) :=
  PO M (AffR M p)

/-- The two settings of the paper. -/
inductive Setting
  | rivalrous
  | nonrivalrous

/-- The demand set `Dem(p)` of a setting: `DemR` (rivalrous) or `DemNR` (non-rivalrous). -/
def Dem (M : Market n m) : Setting → (Fin m → ℝ) → Set (Fin n → Fin m → ℝ)
  | .rivalrous => DemR M
  | .nonrivalrous => DemNR M

/-- `ν`: `1` (rivalrous), `n` (non-rivalrous) (§4.2 table). -/
noncomputable def nu (_M : Market n m) : Setting → ℝ
  | .rivalrous => 1
  | .nonrivalrous => (n : ℝ)

/-- `β`: `B` (rivalrous), `b_min` (non-rivalrous) (§4.2 table). -/
noncomputable def beta (M : Market n m) : Setting → ℝ
  | .rivalrous => M.totalBudget
  | .nonrivalrous => M.bmin

/-- `κ := B / (ν β)` (§4.2 table); it equals `1` (rivalrous) and `b_avg / b_min` (non-rivalrous). -/
noncomputable def kappa (M : Market n m) (s : Setting) : ℝ := M.totalBudget / (nu M s * beta M s)

/-- Seller `j`'s revenue `R_j(p, x) := p_j ∑_i x_{i,j}`. -/
def revenue (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (j : Fin m) : ℝ := p j * ∑ i, x i j

/-- Total revenue `R_all(p, x) := ∑_j R_j(p, x)`. -/
def totalRevenue (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) : ℝ := ∑ j, revenue p x j

/-- An allocation rule for setting `s`: `A(p) ∈ Dem(p)` for every price vector `p ≥ 0`.
(Values of `A` at prices outside the nonnegative orthant are never used.) -/
def IsAllocationRule (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) : Prop :=
  ∀ p : Fin m → ℝ, 0 ≤ p → A p ∈ Dem M s p

/-- A continuous allocation rule: an allocation rule continuous on the closed orthant `ℝ^m_{≥0}`. -/
def IsContinuousAllocationRule (M : Market n m) (s : Setting)
    (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) : Prop :=
  IsAllocationRule M s A ∧ ContinuousOn A {p | 0 ≤ p}

/-- Seller `j`'s revenue under the rule `A`: `R^A_j(p) := R_j(p, A(p))`. -/
def revA (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (j : Fin m) (p : Fin m → ℝ) : ℝ :=
  revenue p (A p) j

/-- Total revenue under the rule `A`: `R_all(p) := R_all(p, A(p))`. -/
def totalRevA (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (p : Fin m → ℝ) : ℝ :=
  totalRevenue p (A p)

/-- Definition 2: `p ∈ ℝ^m_{≥0}` is a `δ`-additive `κ`-RARE for the rule `A` if for every seller
`j` and every deviation `q_j ≥ 0` there is a response `q_{-j} ≥ 0` such that, with
`q = (q_j, q_{-j})` (encoded as `Function.update r j qj`, the `j`-th entry of `r` being ignored),
(1) `R^A_j(q) ≤ κ R^A_j(p) + δ` and (2) `R^A_k(q) ≥ R^A_k((q_j, p_{-j}))` for every `k ≠ j`.
The plain `κ`-RARE is the case `δ = 0`. -/
def IsRARE (A : (Fin m → ℝ) → (Fin n → Fin m → ℝ)) (δ κ : ℝ) (p : Fin m → ℝ) : Prop :=
  0 ≤ p ∧
    ∀ j : Fin m, ∀ qj : ℝ, 0 ≤ qj →
      ∃ r : Fin m → ℝ, (∀ k, k ≠ j → 0 ≤ r k) ∧
        revA A j (Function.update r j qj) ≤ κ * revA A j p + δ ∧
        ∀ k, k ≠ j → revA A k (Function.update p j qj) ≤ revA A k (Function.update r j qj)

/-- The scaled simplex `β∆_m := {x ∈ ℝ^m_{≥0} : ∑_j x_j = β}` (§3.4). -/
def scaledSimplex (m : ℕ) (β : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∑ j, x j = β}

/-- The union of the upper faces of the box `∏_{j ∈ J} [ℓ_j, h_j]` (Lemma 2):
`U := {x ∈ ∏_j [ℓ_j, h_j] : x_i = h_i for some i}`. -/
def upperFaces {ι : Type*} (ℓ h : ι → ℝ) : Set (ι → ℝ) :=
  {x | x ∈ Set.Icc ℓ h ∧ ∃ i, x i = h i}

/-- Security pair of seller `j` (conclusion of Lemma 5): `ρ_j > 0`, `σ_j ≥ ρ_j/ν`, and pricing at
`σ_j` earns at least `ρ_j` against every response `q_{-j} ≥ 0` and every demanded allocation. -/
def IsSecurityPair (M : Market n m) (s : Setting) (j : Fin m) (ρj σj : ℝ) : Prop :=
  0 < ρj ∧ ρj / nu M s ≤ σj ∧
    ∀ r : Fin m → ℝ, (∀ k, k ≠ j → 0 ≤ r k) →
      ∀ x ∈ Dem M s (Function.update r j σj), ρj ≤ revenue (Function.update r j σj) x j

/-- Overpricing bound of seller `j` (conclusion of Lemma 6): `L_j ≥ max(B, σ_j)` and, for all
prices `q ≥ 0` and `x ∈ Dem(q)`, if `q_j > L_j` and `max_{k ≠ j} q_k = B` then
`R_j(q, x) ≤ ρ_j / (2κ)`. The maximum (over a nonempty index set, as `m ≥ 2`) is written as
"every `q_k ≤ B` for `k ≠ j`, with equality for some `k ≠ j`". -/
def IsOverpricingBound (M : Market n m) (s : Setting) (j : Fin m) (ρj σj Lj : ℝ) : Prop :=
  max M.totalBudget σj ≤ Lj ∧
    ∀ q : Fin m → ℝ, 0 ≤ q → ∀ x ∈ Dem M s q,
      Lj < q j → (∀ k, k ≠ j → q k ≤ M.totalBudget) → (∃ k, k ≠ j ∧ q k = M.totalBudget) →
        revenue q x j ≤ ρj / (2 * kappa M s)

end RAREPricing.Existence


