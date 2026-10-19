-- Prove2me | Definitions.Def_LeaseModular_JointChoice_Setting
-- name    : LeaseModular_JointChoice_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:41.9084+00:00
-- url     : https://prove2.me/theorems/589c6dc7-d42b-4177-ab66-4a8cba3fdcc5
-- title:
--   §3–§4 and Appendix, pp. 5–11, 31–36 — durable two-module product, the firm problems SI, SM, LI, LM with their inverse demand, and the cost thresholds
-- statement:
--   This file sets up the steady-state model of Agrawal, Atasu and Ülkü: a monopolist offers a durable product made of two modules, module 1 being the more durable one. Customer valuations $\theta$ are uniform on $[0,1]$, each module contributes half of the valuation, both modules cost $c$ to produce, and the discount factor is $1$.
--
--   **Parameters and standing assumptions.** A parameter record consists of the durabilities $\delta_1,\delta_2$ of the modules under selling, the relative return condition $\gamma$ of off-lease modules, and the production cost $c$. Under leasing the durabilities are $\delta_{1l}=\gamma\delta_1$ and $\delta_{2l}=\gamma\delta_2$. The standing assumptions (pp. 6–8) are
--   $$0<\delta_2<\delta_1<1,\qquad \gamma>0,\qquad \gamma\delta_1<1,\qquad 0<c<\tfrac{1-\delta_2}{2},\qquad c<\tfrac{1-\gamma\delta_2}{2}.$$
--
--   **Selling an integral product (SI).** The firm chooses the quantity $S_n\ge 0$ of new products; the inverse demand is $p_n(S_n)=\tfrac12\big((1-S_n)(2+\delta_1+\delta_2)-2S_n(\delta_1+\delta_2)\big)$ and the profit is $\Pi_{SI}(S_n)=(p_n(S_n)-2c)S_n$.
--
--   **Selling a modular product (SM).** The firm chooses quantities $0\le S_{n1}\le S_{n2}$ of new first and second modules (the gap $S_{n2}-S_{n1}$ is the segment of customers holding a used first and a new second module, the UN segment). With $p_{n1}(S_{n1})=\tfrac12\big((1-S_{n1})(1+2\delta_2+\delta_1)-2S_{n1}(\delta_1+\delta_2)\big)$ and $p_{n2}(S_{n2})=\tfrac12(1-S_{n2})(1-\delta_2)$ the profit is
--   $$\Pi_{SM}=(p_{n1}(S_{n1})-c)S_{n1}+(p_{n2}(S_{n2})-c)S_{n2}.$$
--
--   **Leasing an integral product (LI).** The firm chooses lease quantities $0\le L_u\le L_n$ of used and new products, with $r_n=1-L_n-\tfrac{\delta_{1l}+\delta_{2l}}{2}L_u$, $r_u=\tfrac{\delta_{1l}+\delta_{2l}}{2}(1-L_n-L_u)$ and profit $\Pi_{LI}=(r_n-2c)L_n+r_uL_u$.
--
--   **Leasing a modular product (LM).** The firm chooses $L_{nn},L_{un},L_{uu}\ge 0$ (new, blended with a used first and new second module, used) subject to the supply constraint $L_{uu}+L_{un}\le L_{nn}$, with
--   $$r_{nn}=1-L_{nn}-\tfrac{\delta_{1l}+1}{2}L_{un}-\tfrac{\delta_{1l}+\delta_{2l}}{2}L_{uu},\quad r_{un}=\tfrac{\delta_{1l}+1}{2}(1-L_{nn}-L_{un})-\tfrac{\delta_{1l}+\delta_{2l}}{2}L_{uu},\quad r_{uu}=\tfrac{\delta_{1l}+\delta_{2l}}{2}(1-L_{nn}-L_{un}-L_{uu}),$$
--   and profit $\Pi_{LM}=(r_{nn}-2c)L_{nn}+(r_{un}-c)L_{un}+r_{uu}L_{uu}$.
--
--   For each problem, "$v$ is the optimal profit" means that $v$ is the maximum of the profit over the feasible set, and that it is attained. An optimal decision is a feasible point attaining it.
--
--   **Thresholds** (Appendix, pp. 33–36), with $a=\delta_1+\delta_2$:
--   $$C_{SM}=\frac{(1-\delta_2)a}{3\delta_1+5\delta_2},\quad C_{LI}=\frac{2-\gamma a}{8},\quad C_{LM1}=\frac{1-\gamma\delta_1}{4},\quad C_{LM2}=\frac{(1-\gamma\delta_2)a}{3\delta_1+5\delta_2},$$
--   $$D_S=\tfrac12\Big(1-5c-\delta_1+\sqrt{25c^2+(1+\delta_1)^2-2c(5+\delta_1)}\Big),\quad D_L=\tfrac1{2\gamma}\Big(1-5c-\gamma\delta_1+\sqrt{25c^2+(1+\gamma\delta_1)^2-2c(5+\gamma\delta_1)}\Big),$$
--   $$C_I=\frac{2-a}{4\Big(2+\sqrt{\frac{(1-\gamma)(2+3a)}{2-\gamma a}}\Big)},\qquad C_M=\frac{(1-\delta_1)a}{4a+(8a+2(1-\delta_1))\sqrt{\frac{(1-\gamma)a\,(a-\delta_1\delta_2(2+\gamma(2-\delta_1))+\gamma\delta_1\delta_2^2)}{(1-\gamma\delta_1)(1-\delta_2)(1-\gamma\delta_2)(1+3\delta_1+4\delta_2)}}}.$$
--
--   These objects are the common ground of every statement in the mission: the optimal profits $\Pi^*_{SI},\Pi^*_{SM},\Pi^*_{LI},\Pi^*_{LM}$ are compared against the thresholds.
--
--   **Formalization Note.** Two printed formulas are corrected. (i) The Appendix (p. 31) prints the SI inverse demand with $-2S_n(1+\delta_1+\delta_2)$; the term $-2S_n(\delta_1+\delta_2)$ is the one that yields the printed $S^*_n$, $p^*_n$ and $\Pi^*_{SI}$ and agrees with the no-UN formula of p. 33. (ii) p. 35 prints $C_{LM2}$ with an extra factor $\gamma$ in the denominator; the corrected form is the one forced by the Case 4 multiplier, the printed difference $C_{LI}-C_{LM2}$ and $D_L$ on p. 36, and with the printed form Lemma 2 and Proposition 3 fail for $\gamma\ne1$. The SM feasible set $0\le S_{n1}\le S_{n2}$ covers both regimes of p. 33 (with and without a UN segment): on the diagonal the profit is the no-UN profit. The LM problem is the §4.4 problem, in which the NU product is already excluded. $0<c$ is made explicit (at $c=0$, $\Pi^*_{LM}=\Pi^*_{LI}$, p. 36). Square roots use `Real.sqrt`, which returns $0$ on negative input; the radicands of $C_I$ and $C_M$ are nonnegative for $\gamma\le1$, the only range where they are used. $\alpha=1/2$, $c_1=c_2=c$ and $\rho=1$ are fixed, not parameters.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), §3–§4 and Appendix, pp. 5–11 (standing assumptions pp. 6–8, footnote 7), 31–36 (inverse demand pp. 31, 33, 34; C_SM, D_S p. 33; C_LI p. 34; C_LM1, C_LM2 p. 35; D_L, C_I, C_M p. 36)

import Mathlib

namespace LeaseModular.JointChoice

/-! # Leasing, modularity and the circular economy: the four firm problems

Agrawal, Atasu & Ülkü, *Leasing, Modularity, and the Circular Economy*, author manuscript
(Management Science, doi:10.1287/mnsc.2020.3829), §3 (pp. 5–8), §4 (pp. 8–11) and Appendix
(pp. 31–36).

A monopolist offers a durable product made of two modules. Module 1 is the more durable one.
Customer valuations are uniform on `[0, 1]`, each module contributes half of the valuation
(`α = 1/2`), both modules cost `c` to produce (`c₁ = c₂ = c`), and the discount factor is
`ρ = 1`; these are fixed, as in the paper's main model. The firm sells or leases (business model
`S`/`L`) an integral or a modular product (architecture `I`/`M`), which gives the four steady-state
problems SI, SM, LI, LM of §4, each written in quantities with the printed inverse demand
functions. -/

/-- The model parameters: the durabilities `δ₁, δ₂` of the two modules under selling, the relative
return condition `γ` of off-lease modules (durability under leasing is `δ_kl = γ δ_k`, p. 7), and
the per-module production cost `c`. -/
structure Params where
  δ₁ : ℝ
  δ₂ : ℝ
  γ : ℝ
  c : ℝ

/-- The standing assumptions of §3 (pp. 6–8): `δ_ki ∈ (0,1)` with `δ_1i > δ_2i` for both business
models, `γ > 0`, `γ δ₁ < 1` (footnote 7: `δ_1l < 1`), and `c < (1 − δ_2i)/2` for `i ∈ {L, S}`
(p. 8). The cost is a production cost, so `0 < c` is made explicit. -/
structure Standing (P : Params) : Prop where
  δ₂_pos : 0 < P.δ₂
  δ₂_lt_δ₁ : P.δ₂ < P.δ₁
  δ₁_lt_one : P.δ₁ < 1
  γ_pos : 0 < P.γ
  γδ₁_lt_one : P.γ * P.δ₁ < 1
  c_pos : 0 < P.c
  c_lt_sell : P.c < (1 - P.δ₂) / 2
  c_lt_lease : P.c < (1 - P.γ * P.δ₂) / 2

/-- Durability of module 1 under leasing, `δ_1l = γ δ₁` (p. 7). -/
def δ₁l (P : Params) : ℝ := P.γ * P.δ₁

/-- Durability of module 2 under leasing, `δ_2l = γ δ₂` (p. 7). -/
def δ₂l (P : Params) : ℝ := P.γ * P.δ₂

/-! ## Selling an integral product (SI), §4.1 p. 9 and Appendix p. 31 -/

/-- Inverse demand for new integral products under selling,
`p_n(S_n) = ((1 − S_n)(2 + δ₁ + δ₂) − 2 S_n (δ₁ + δ₂)) / 2`. The Appendix (p. 31) prints
`−2S_n(1+δ₁+δ₂)`; the term `−2S_n(δ₁+δ₂)` is the one that yields the printed `S*_n`, `p*_n` and
`Π*_SI` and the p. 33 no-UN formula. -/
noncomputable def pSI (P : Params) (S : ℝ) : ℝ :=
  ((1 - S) * (2 + P.δ₁ + P.δ₂) - 2 * S * (P.δ₁ + P.δ₂)) / 2

/-- The SI profit `Π_SI(S_n) = (p_n(S_n) − 2c) S_n`. -/
noncomputable def profitSI (P : Params) (S : ℝ) : ℝ := (pSI P S - 2 * P.c) * S

/-- Feasible SI quantities: `S_n ≥ 0`. -/
def feasSI : Set ℝ := Set.Ici 0

/-- `v` is the optimal SI profit `Π*_SI`: the maximum of `Π_SI` over `S_n ≥ 0`, attained. -/
def IsOptSI (P : Params) (v : ℝ) : Prop := IsGreatest (profitSI P '' feasSI) v

/-! ## Selling a modular product (SM), §4.3 p. 10 and Appendix pp. 32–33 -/

/-- Quantities sold under SM: new first modules `n1 = S_n1` and new second modules `n2 = S_n2`. -/
structure SMQty where
  n1 : ℝ
  n2 : ℝ

/-- Inverse demand for new first modules (p. 33),
`p_n1(S_n1) = ((1 − S_n1)(1 + 2δ₂ + δ₁) − 2 S_n1 (δ₁ + δ₂)) / 2`. -/
noncomputable def pSM1 (P : Params) (S₁ : ℝ) : ℝ :=
  ((1 - S₁) * (1 + 2 * P.δ₂ + P.δ₁) - 2 * S₁ * (P.δ₁ + P.δ₂)) / 2

/-- Inverse demand for new second modules (p. 33), `p_n2(S_n2) = (1 − S_n2)(1 − δ₂) / 2`. -/
noncomputable def pSM2 (P : Params) (S₂ : ℝ) : ℝ := (1 - S₂) * (1 - P.δ₂) / 2

/-- The SM profit `Π_SM(S_n1, S_n2) = (p_n1(S_n1) − c) S_n1 + (p_n2(S_n2) − c) S_n2`. On the
diagonal `S_n1 = S_n2 = S` it equals the p. 33 no-UN profit `(p_n(S) − 2c) S` with
`p_n = ((1 − S)(2 + δ₁ + δ₂) − 2S(δ₁ + δ₂))/2`, so one domain covers both regimes of p. 33. -/
noncomputable def profitSM (P : Params) (x : SMQty) : ℝ :=
  (pSM1 P x.n1 - P.c) * x.n1 + (pSM2 P x.n2 - P.c) * x.n2

/-- Feasible SM quantities: `0 ≤ S_n1 ≤ S_n2`; the difference `S_n2 − S_n1` is the UN segment
(customers with a used first and a new second module). `S_n1 ≤ S_n2` is the regime condition
`p_n1 ≥ P_b1(p_n2)` of p. 32, and `S_n1 = S_n2` is the regime without a UN segment. -/
def feasSM : Set SMQty := {x | 0 ≤ x.n1 ∧ x.n1 ≤ x.n2}

/-- `v` is the optimal SM profit `Π*_SM`, attained. -/
def IsOptSM (P : Params) (v : ℝ) : Prop := IsGreatest (profitSM P '' feasSM) v

/-- `x` is an optimal SM decision. -/
def IsMaxSM (P : Params) (x : SMQty) : Prop :=
  x ∈ feasSM ∧ ∀ y ∈ feasSM, profitSM P y ≤ profitSM P x

/-! ## Leasing an integral product (LI), §4.2 p. 9 -/

/-- Lease quantities under LI: new products `n = L_n` and used products `u = L_u`. -/
structure LIQty where
  n : ℝ
  u : ℝ

/-- Inverse demand for new leases, `r_n(L_n, L_u) = 1 − L_n − ((δ_1l + δ_2l)/2) L_u`. -/
noncomputable def rLIn (P : Params) (x : LIQty) : ℝ :=
  1 - x.n - ((δ₁l P + δ₂l P) / 2) * x.u

/-- Inverse demand for used leases, `r_u(L_n, L_u) = ((δ_1l + δ_2l)/2)(1 − L_n − L_u)`. -/
noncomputable def rLIu (P : Params) (x : LIQty) : ℝ :=
  ((δ₁l P + δ₂l P) / 2) * (1 - x.n - x.u)

/-- The LI profit `Π_LI(L_n, L_u) = (r_n − 2c) L_n + r_u L_u`. -/
noncomputable def profitLI (P : Params) (x : LIQty) : ℝ :=
  (rLIn P x - 2 * P.c) * x.n + rLIu P x * x.u

/-- Feasible LI quantities: `0 ≤ L_u ≤ L_n`. -/
def feasLI : Set LIQty := {x | 0 ≤ x.u ∧ x.u ≤ x.n}

/-- `v` is the optimal LI profit `Π*_LI`, attained. -/
def IsOptLI (P : Params) (v : ℝ) : Prop := IsGreatest (profitLI P '' feasLI) v

/-- `x` is an optimal LI decision. -/
def IsMaxLI (P : Params) (x : LIQty) : Prop :=
  x ∈ feasLI ∧ ∀ y ∈ feasLI, profitLI P y ≤ profitLI P x

/-! ## Leasing a modular product (LM), §4.4 p. 11 and Appendix p. 34 -/

/-- Lease quantities under LM: completely new products `nn = L_nn`, blended products with a used
first and a new second module `un = L_un`, and completely used products `uu = L_uu`. -/
structure LMQty where
  nn : ℝ
  un : ℝ
  uu : ℝ

/-- `r_nn = 1 − L_nn − ((δ_1l + 1)/2) L_un − ((δ_1l + δ_2l)/2) L_uu` (p. 34 with `L_nu = 0`). -/
noncomputable def rLMnn (P : Params) (x : LMQty) : ℝ :=
  1 - x.nn - ((δ₁l P + 1) / 2) * x.un - ((δ₁l P + δ₂l P) / 2) * x.uu

/-- `r_un = ((δ_1l + 1)/2)(1 − L_nn − L_un) − ((δ_1l + δ_2l)/2) L_uu` (p. 34 with `L_nu = 0`). -/
noncomputable def rLMun (P : Params) (x : LMQty) : ℝ :=
  ((δ₁l P + 1) / 2) * (1 - x.nn - x.un) - ((δ₁l P + δ₂l P) / 2) * x.uu

/-- `r_uu = ((δ_1l + δ_2l)/2)(1 − L_nn − L_un − L_uu)` (p. 34 with `L_nu = 0`). -/
noncomputable def rLMuu (P : Params) (x : LMQty) : ℝ :=
  ((δ₁l P + δ₂l P) / 2) * (1 - x.nn - x.un - x.uu)

/-- The LM profit `Π_LM = (r_nn − 2c) L_nn + (r_un − c) L_un + r_uu L_uu` (p. 11). -/
noncomputable def profitLM (P : Params) (x : LMQty) : ℝ :=
  (rLMnn P x - 2 * P.c) * x.nn + (rLMun P x - P.c) * x.un + rLMuu P x * x.uu

/-- Feasible LM quantities (p. 11): `L_nn, L_un, L_uu ≥ 0` and the supply constraint for the
more-durable module, `L_uu + L_un ≤ L_nn`. -/
def feasLM : Set LMQty := {x | 0 ≤ x.nn ∧ 0 ≤ x.un ∧ 0 ≤ x.uu ∧ x.uu + x.un ≤ x.nn}

/-- `v` is the optimal LM profit `Π*_LM`, attained. -/
def IsOptLM (P : Params) (v : ℝ) : Prop := IsGreatest (profitLM P '' feasLM) v

/-- `x` is an optimal LM decision. -/
def IsMaxLM (P : Params) (x : LMQty) : Prop :=
  x ∈ feasLM ∧ ∀ y ∈ feasLM, profitLM P y ≤ profitLM P x

/-! ## Cost and durability thresholds, Appendix pp. 33–36 (closed forms as printed) -/

/-- `C_SM(δ₁, δ₂) = (1 − δ₂)(δ₁ + δ₂)/(3δ₁ + 5δ₂)` (p. 33). -/
noncomputable def CSM (δ₁ δ₂ : ℝ) : ℝ := (1 - δ₂) * (δ₁ + δ₂) / (3 * δ₁ + 5 * δ₂)

/-- `D_S(δ₁, c) = (1/2)(1 − 5c − δ₁ + √(25c² + (1 + δ₁)² − 2c(5 + δ₁)))` (p. 33). -/
noncomputable def DS (δ₁ c : ℝ) : ℝ :=
  (1 / 2) * (1 - 5 * c - δ₁ + Real.sqrt (25 * c ^ 2 + (1 + δ₁) ^ 2 - 2 * c * (5 + δ₁)))

/-- `C_LI(δ₁, δ₂, γ) = (2 − γ(δ₁ + δ₂))/8` (p. 34). -/
noncomputable def CLI (δ₁ δ₂ γ : ℝ) : ℝ := (2 - γ * (δ₁ + δ₂)) / 8

/-- `C_LM1(δ₁, γ) = (1 − γδ₁)/4` (p. 35). -/
noncomputable def CLM1 (δ₁ γ : ℝ) : ℝ := (1 - γ * δ₁) / 4

/-- `C_LM2(δ₁, δ₂, γ) = (1 − γδ₂)(δ₁ + δ₂)/(3δ₁ + 5δ₂)`. **Corrected**: p. 35 prints an extra
factor `γ` in the denominator, `(1 − γδ₂)(δ₁ + δ₂)/(γ(3δ₁ + 5δ₂))`. The corrected form is the one
given by the Case 4 multiplier `μ₂ ≥ 0` (p. 35), by the printed difference
`C_LI − C_LM2 = −(δ₁ − δ₂)(2 + 3γ(δ₁ + δ₂))/(8(3δ₁ + 5δ₂))` and by `D_L` (p. 36); with the printed
form Lemma 2 and Proposition 3 fail for `γ ≠ 1`. -/
noncomputable def CLM2 (δ₁ δ₂ γ : ℝ) : ℝ := (1 - γ * δ₂) * (δ₁ + δ₂) / (3 * δ₁ + 5 * δ₂)

/-- `D_L(δ₁, γ, c) = (1/(2γ))(1 − 5c − γδ₁ + √(25c² + (1 + γδ₁)² − 2c(5 + γδ₁)))` (p. 36). -/
noncomputable def DL (δ₁ γ c : ℝ) : ℝ :=
  (1 / (2 * γ)) *
    (1 - 5 * c - γ * δ₁ + Real.sqrt (25 * c ^ 2 + (1 + γ * δ₁) ^ 2 - 2 * c * (5 + γ * δ₁)))

/-- `C_I(δ₁, δ₂, γ) = (2 − δ₁ − δ₂)/(4(2 + √((1 − γ)(2 + 3δ₁ + 3δ₂)/(2 − γ(δ₁ + δ₂)))))` (p. 36).
The radicand is nonnegative for `γ ≤ 1`, the only range where the paper uses `C_I`
(`Real.sqrt` returns `0` on negative input). -/
noncomputable def CI (δ₁ δ₂ γ : ℝ) : ℝ :=
  (2 - δ₁ - δ₂) /
    (4 * (2 + Real.sqrt ((1 - γ) * (2 + 3 * δ₁ + 3 * δ₂) / (2 - γ * (δ₁ + δ₂)))))

/-- `C_M(δ₁, δ₂, γ) = (1 − δ₁)(δ₁ + δ₂) / (4(δ₁ + δ₂) + (8(δ₁ + δ₂) + 2(1 − δ₁)) √R)` with
`R = (1 − γ)(δ₁ + δ₂)(δ₁ + δ₂ − δ₁δ₂(2 + γ(2 − δ₁)) + γδ₁δ₂²) /
((1 − γδ₁)(1 − δ₂)(1 − γδ₂)(1 + 3δ₁ + 4δ₂))` (p. 36). `R ≥ 0` for `γ ≤ 1`, the only range where
the paper uses `C_M`. -/
noncomputable def CM (δ₁ δ₂ γ : ℝ) : ℝ :=
  (1 - δ₁) * (δ₁ + δ₂) /
    (4 * (δ₁ + δ₂) + (8 * (δ₁ + δ₂) + 2 * (1 - δ₁)) *
      Real.sqrt ((1 - γ) * (δ₁ + δ₂) *
          (δ₁ + δ₂ - δ₁ * δ₂ * (2 + γ * (2 - δ₁)) + γ * δ₁ * δ₂ ^ 2) /
        ((1 - γ * δ₁) * (1 - δ₂) * (1 - γ * δ₂) * (1 + 3 * δ₁ + 4 * δ₂))))

end LeaseModular.JointChoice


