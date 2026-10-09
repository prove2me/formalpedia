-- Prove2me | Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm
-- name    : LimitedPriceChanges_AlgorithmI_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:25.585107+00:00
-- url     : https://prove2.me/theorems/129781b4-f195-4178-a317-ac9da38dade7
-- title:
--   p. 9 — Algorithm-I (m price changes): stages, censored MLE (5), plug-in (6), path law and regret R(T)
-- statement:
--   This file defines Algorithm-I, the law of the demand path it induces, and its regret.
--
--   **Inputs.** A price-change budget $m$, an initial price $\hat p_1$, an initial order-up-to level $\hat y_1$, an integer $\Delta$, a price selection $p^*_y(z)$, a maximum-likelihood selection and an order-up-to selection (below). The *valid* inputs have $m\ge1$, $\hat p_1\in\mathcal P$, $\hat y_1\in\mathcal Y$, $\Delta\ge1$.
--
--   **Stages (Step 0).** For horizon $T$, $I_i=\lceil T^{i/(m+1)}\rceil$ for $i=1,\dots,m$, $I_{m+1}=T-\sum_{i=1}^mI_i$, $t_1=0$ and $t_i=\sum_{j=1}^{i-1}I_j$; stage $i$ consists of periods $t_i+1,\dots,t_{i+1}$.
--
--   **Step 1.** In stage $i$ the price is $p_t=\hat p_i$ and the level is $y_t=\max\{x_t,\tilde y_i\}$, with $x_1=0$, $x_{t+1}=\max\{y_t-d_t,0\}$ and
--   $$
--   \tilde y_i=\begin{cases}\hat y_i,&\hat y_i>d^l,\\ \min\{\max\{\hat y_i+\Delta,y^l\},y^h\},&\hat y_i=d^l.\end{cases}
--   $$
--   The firm observes only the sales $\min\{d_t,y_t\}$.
--
--   **Step 2.** The estimate $\hat z_i$ maximizes over $\mathcal Z$ the censored likelihood of stage $i$,
--   $$
--   \prod_{t=t_i+1}^{t_{i+1}}\tilde f_{y_t}\big(\min\{d_t,y_t\};\hat p_i,z\big),\qquad \tilde f_y(s;p,z)=\begin{cases}f(s;p,z),&s<y,\\1-F(y-1;p,z),&s=y,\end{cases}
--   $$
--   which is the exponential of the objective of (5). A *maximum-likelihood selection* returns, for every price in $\mathcal P$ and every list of observations $(y_t,\min\{d_t,y_t\})$, a maximizer in $\mathcal Z$.
--
--   **Step 3.** $\hat y_{i+1}\in\mathcal Y$ maximizes $y\mapsto G(p^*_y(\hat z_i),y,\hat z_i)$ (an *order-up-to selection*) and $\hat p_{i+1}=p^*_{\hat y_{i+1}}(\hat z_i)$, a solution of (6).
--
--   **Path law and regret.** Given the true $z$, a demand path $d=(d_1,\dots,d_T)$ has probability $\prod_{t=1}^Tf(d_t;p_t,z)$, because $d_t$ has pmf $f(\cdot;p_t,z)$ given the past and $p_t$ is a function of the past. Expectations and probabilities are sums over paths with these weights. The regret is
--   $$
--   R(T)=\sum_{t=1}^T\mathbb E\big[G^*(z)-G(p_t,y_t,z)\big]=T\cdot G^*(z)-\mathbb E[V^{\phi}(T,z)] .
--   $$
--   The standing hypotheses of §2–§3 at the true $z$ (membership $z\in\mathcal Z$, the price selection, $\mathbb E[D]>0$, Assumption A, optimal levels above $d^l$, Definition 1, Assumption 1) are collected as `Standing`.
--
--   **Formalization Note** Lean periods are 0-based: Lean period $s$ is the paper's period $s+1$, and the horizon-$T$ path is $d:\mathrm{Fin}\,T\to\mathbb N$; stages keep the paper's indices. The algorithm reads the demand only through the sales $\min\{d_t,y_t\}$, and the carried inventory is computed as $y_t-\min\{d_t,y_t\}=(y_t-d_t)^+$. Step 2's "arg max" and Step 3's "arg max" are arbitrary selections with the maximizing property (any maximizer works); the product likelihood avoids $\log0$, and for every list a maximizer exists by compactness of $\mathcal Z$. Step 3 is read through the price selection $p^*$: the pair $(p^*_{\hat y}(\hat z),\hat y)$ is a joint maximizer of $G(\cdot,\cdot,\hat z)$, and it is the decision the proof of Theorem B1 analyses. $I_{m+1}$ uses truncated natural subtraction (positive for large $T$), $T^{i/(m+1)}$ is a real power and $\lceil\cdot\rceil$ the natural ceiling. Regret and probabilities are sums in $[0,\infty]$; every regret summand is nonnegative. The structure field `Δ` is the input $\Delta$.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 5 ((1), dynamics), p. 6 (R(T)), p. 9 (Algorithm-I, (5), (6)), p. 24 (R(T) = Σ_t 𝔼[G*(z) − G(p_t, y_t, z)]), p. 27 ((32))

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Model

namespace LimitedPriceChanges.AlgorithmI

/-! # Algorithm-I, its demand-path law and its regret

Chen, Chao and Wang, *Data-Based Dynamic Pricing and Inventory Control with Censored Demand and
Limited Price Changes*, SSRN 2700747 (revision of 2020-02-10), p. 9 (Algorithm-I, (5), (6)),
p. 6 (regret) and p. 24 (`R(T) = ∑_t 𝔼[G*(z) − G(p_t, y_t, z)]`).

Periods are 0-based in Lean: Lean period `s` is the paper's period `s + 1`. A demand path of
horizon `T` is `d : Fin T → ℕ`. Stages `i = 1, …, m + 1` keep the paper's indexing; stage `i`
consists of the Lean periods `s` with `tᵢ ≤ s < tᵢ₊₁` (the paper's periods `tᵢ + 1, …, tᵢ₊₁`).
The law of the demand path under the algorithm is `∏ₛ f(d_s; p_s, z)`, because the demand of a
period has pmf `f(·; p_s, z)` given the past and the price `p_s` is a function of the past;
expectations and probabilities are sums over paths with these weights. -/

/-- The likelihood (32), p. 27, of a stage's censored observations at price `p`: each observation
is a pair `(y, s)` of an order-up-to level and the sales `s = min{d, y}`; it contributes
`f(s; p, z)` if `s < y` (demand observed exactly, `d = s < y`) and the tail mass
`1 − F(y − 1; p, z)` if `s = y` (a stockout, `d ≥ y`). This is `exp` of the objective of (5)
whenever all factors are positive. -/
noncomputable def Model.likelihood (S : Model) (p : ℝ) (L : List (ℕ × ℕ)) (z : ℝ) : ℝ :=
  (L.map (fun o => if o.2 < o.1 then S.f o.2 p z else S.tail o.1 p z)).prod

/-- `mle` is a maximum-likelihood selection for (5): for every price `p ∈ 𝒫` and every list of
censored observations `L`, `mle p L ∈ 𝒵` maximizes the likelihood over `𝒵`. -/
def Model.IsMLE (S : Model) (mle : ℝ → List (ℕ × ℕ) → ℝ) : Prop :=
  ∀ p ∈ S.P, ∀ L : List (ℕ × ℕ), mle p L ∈ S.Z ∧
    ∀ z' ∈ S.Z, S.likelihood p L z' ≤ S.likelihood p L (mle p L)

/-- `yplug` is the order-up-to part of a solution of (6): for every `z' ∈ 𝒵`, `yplug z' ∈ 𝒴`
maximizes `y ↦ G(p*_y(z'), y, z')` over `𝒴`. The plug-in decision of Step 3 is then
`(p*_{ŷ}(z'), ŷ)` with `ŷ = yplug z'`, a joint maximizer of `G(·, ·, z')` over `𝒫 × 𝒴`. -/
def Model.IsPlugIn (S : Model) (pstar : ℕ → ℝ → ℝ) (yplug : ℝ → ℕ) : Prop :=
  IsLevelSelection S.Y S.Z S.G pstar yplug

/-- An instance of Algorithm-I (p. 9) on the model `S`: the price-change budget `m`, the inputs
`p̂₁`, `ŷ₁`, `Δ`, the price selection `pstar = p*_·(·)` used in Step 3, the maximum-likelihood
selection `mle` of Step 2 and the order-up-to selection `yplug` of Step 3. -/
structure Alg (S : Model) where
  m : ℕ
  p1 : ℝ
  y1 : ℕ
  Δ : ℕ
  pstar : ℕ → ℝ → ℝ
  mle : ℝ → List (ℕ × ℕ) → ℝ
  yplug : ℝ → ℕ

namespace Alg

variable {S : Model} (A : Alg S)

/-- Step 0: `⌈T^{i/(m+1)}⌉`. -/
noncomputable def ceilLen (T i : ℕ) : ℕ := ⌈(T : ℝ) ^ ((i : ℝ) / ((A.m : ℝ) + 1))⌉₊

/-- Step 0: the stage lengths `Iᵢ = ⌈T^{i/(m+1)}⌉` for `i ≤ m` and
`I_{m+1} = T − ∑_{i=1}^m Iᵢ` (natural subtraction; positive for `T` large). Only
`i ∈ {1, …, m + 1}` is used. -/
noncomputable def stageLen (T i : ℕ) : ℕ :=
  if i ≤ A.m then A.ceilLen T i else T - ∑ j ∈ Finset.Icc 1 A.m, A.ceilLen T j

/-- Step 0: `tᵢ = ∑_{j=1}^{i−1} I_j` (so `t₁ = 0`); in Lean, stage `i` starts at period `tᵢ`. -/
noncomputable def stageStart (T i : ℕ) : ℕ := ∑ j ∈ Finset.Ico 1 i, A.stageLen T j

/-- The stage `i ∈ {1, …, m + 1}` of the (0-based) period `s`: one plus the number of stages
`j ≤ m` that have ended by period `s` (i.e. `t_{j+1} ≤ s`). -/
noncomputable def stageOf (T s : ℕ) : ℕ :=
  1 + ((Finset.Icc 1 A.m).filter (fun j => A.stageStart T (j + 1) ≤ s)).card

/-- Step 1 exploration: `ỹ = ŷ` if `ŷ > dl`, and `min{max{ŷ + Δ, yl}, yh}` if `ŷ = dl`. -/
def ytildeOf (yhat : ℕ) : ℕ :=
  if S.dl < yhat then yhat else min (max (yhat + A.Δ) S.yl) S.yh

/-- Run Step 1 for `n` consecutive periods starting at period `s` with carried inventory `x`
and target `ỹ`: each period orders up to `y = max{x, ỹ}`, observes the sales `min{d, y}`,
and carries `x' = y − min{d, y} = (y − d)⁺`. Returns the list of observations `(y, min{d, y})`
in time order and the inventory carried out of the last period. -/
def runStage (d : ℕ → ℕ) (ytil : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) × ℕ
  | _, 0, x => ([], x)
  | s, n + 1, x =>
      let y := max x ytil
      let r := runStage d ytil (s + 1) n (y - min (d s) y)
      ((y, min (d s) y) :: r.1, r.2)

/-- The state at the start of stage `k + 1`: `(p̂_{k+1}, ŷ_{k+1}, x_{t_{k+1}})`, the price and
the order-up-to target of the stage and the inventory carried into its first period. Stage 1
uses the inputs and `x = 0`; stage `k + 2` uses `ẑ_{k+1}`, the MLE (5) of the observations of
stage `k + 1`, through (6): `ŷ_{k+2} = yplug ẑ_{k+1}` and `p̂_{k+2} = p*_{ŷ_{k+2}}(ẑ_{k+1})`. -/
noncomputable def stageState (T : ℕ) (d : ℕ → ℕ) : ℕ → ℝ × ℕ × ℕ
  | 0 => (A.p1, A.y1, 0)
  | k + 1 =>
      let st := stageState T d k
      let r := runStage d (A.ytildeOf st.2.1) (A.stageStart T (k + 1)) (A.stageLen T (k + 1))
        st.2.2
      let zk := A.mle st.1 r.1
      let yk := A.yplug zk
      (A.pstar yk zk, yk, r.2)

/-- The demand path `d : Fin T → ℕ` extended by `0` after the horizon. -/
def extend {T : ℕ} (d : Fin T → ℕ) : ℕ → ℕ := fun s => if h : s < T then d ⟨s, h⟩ else 0

/-- `p̂ᵢ`, the price of stage `i ≥ 1`. -/
noncomputable def phat (T i : ℕ) (d : Fin T → ℕ) : ℝ := (A.stageState T (extend d) (i - 1)).1

/-- `ŷᵢ`, the order-up-to target of stage `i ≥ 1` computed in Step 3. -/
noncomputable def yhat (T i : ℕ) (d : Fin T → ℕ) : ℕ := (A.stageState T (extend d) (i - 1)).2.1

/-- `ỹᵢ`, the order-up-to target of stage `i ≥ 1` after the exploration of Step 1. -/
noncomputable def ytilde (T i : ℕ) (d : Fin T → ℕ) : ℕ := A.ytildeOf (A.yhat T i d)

/-- The censored observations `(y_t, min{d_t, y_t})` of stage `i ≥ 1`, in time order. -/
noncomputable def observations (T i : ℕ) (d : Fin T → ℕ) : List (ℕ × ℕ) :=
  (runStage (extend d) (A.ytilde T i d) (A.stageStart T i) (A.stageLen T i)
    (A.stageState T (extend d) (i - 1)).2.2).1

/-- `ẑᵢ`, the maximum-likelihood estimate (5) computed at the end of stage `i ≥ 1` from that
stage's censored observations at the stage's price `p̂ᵢ`. -/
noncomputable def zhat (T i : ℕ) (d : Fin T → ℕ) : ℝ := A.mle (A.phat T i d) (A.observations T i d)

/-- The price `p_s` charged in (0-based) period `s`: the price of its stage. -/
noncomputable def price (T : ℕ) (s : Fin T) (d : Fin T → ℕ) : ℝ := A.phat T (A.stageOf T s) d

/-- The order-up-to level `y_s = max{x_s, ỹᵢ}` of (0-based) period `s` in stage `i`, where `x_s`
is obtained by running Step 1 from the start of stage `i` up to period `s`. -/
noncomputable def level (T : ℕ) (s : Fin T) (d : Fin T → ℕ) : ℕ :=
  let i := A.stageOf T s
  max (runStage (extend d) (A.ytilde T i d) (A.stageStart T i) ((s : ℕ) - A.stageStart T i)
    (A.stageState T (extend d) (i - 1)).2.2).2 (A.ytilde T i d)

/-- The probability weight `∏ₛ f(d_s; p_s, z)` of the demand path `d` under Algorithm-I when
the true parameter is `z`. -/
noncomputable def pathWeight (z : ℝ) (T : ℕ) (d : Fin T → ℕ) : ENNReal :=
  ∏ s : Fin T, ENNReal.ofReal (S.f (d s) (A.price T s d) z)

/-- `𝔼[X] = ∑_d ℙ(d) X(d)` for a nonnegative path functional `X`. -/
noncomputable def expect (z : ℝ) (T : ℕ) (X : (Fin T → ℕ) → ENNReal) : ENNReal :=
  ∑' d : Fin T → ℕ, A.pathWeight z T d * X d

/-- `ℙ(E) = ∑_{d ∈ E} ℙ(d)` for a set `E` of demand paths. -/
noncomputable def prob (z : ℝ) (T : ℕ) (E : Set (Fin T → ℕ)) : ENNReal :=
  ∑' d : Fin T → ℕ, E.indicator (A.pathWeight z T) d

/-- The regret of Algorithm-I over horizon `T` (p. 6, in the form of p. 24):
`R(T) = ∑_{t=1}^T 𝔼[G*(z) − G(p_t, y_t, z)]`. Each summand is nonnegative, since `G*(z)` is the
maximum of `G(·, ·, z)` over `𝒫 × 𝒴` and `(p_t, y_t) ∈ 𝒫 × 𝒴`. -/
noncomputable def regret (z : ℝ) (T : ℕ) : ENNReal :=
  A.expect z T (fun d => ∑ s : Fin T,
    ENNReal.ofReal (S.Gstar A.pstar z - S.G (A.price T s d) (A.level T s d) z))

/-- The standing conditions on the algorithm's inputs and selections (p. 9): `m ≥ 1`,
`p̂₁ ∈ 𝒫`, `ŷ₁ ∈ 𝒴`, `Δ ≥ 1`; `mle` is a maximum-likelihood selection for (5) and `yplug`
an order-up-to selection for (6). -/
structure Valid : Prop where
  one_le_m : 1 ≤ A.m
  p1_mem : A.p1 ∈ S.P
  y1_mem : A.y1 ∈ S.Y
  one_le_Δ : 1 ≤ A.Δ
  mle : S.IsMLE A.mle
  plugIn : S.IsPlugIn A.pstar A.yplug

end Alg

/-- The standing hypotheses of §2–§3 on the model `S` at the true parameter `z`, for the price
selection `pstar`: `z ∈ 𝒵`; `pstar` is the price selection `p*_y(·)`; `𝔼[D(p, z)] > 0`
(p. 5); Assumption A (p. 7); every optimal order-up-to level exceeds `dl` (p. 7);
Definition 1, well-separated (p. 8); Assumption 1 (p. 8). -/
structure Model.Standing (S : Model) (pstar : ℕ → ℝ → ℝ) (z : ℝ) : Prop where
  z_mem : z ∈ S.Z
  priceSelection : S.IsPriceSelection pstar
  meanPos : S.MeanPos z
  assumptionA : S.AssumptionA pstar z
  optLevel : S.OptLevelAboveDl pstar z
  wellSeparated : S.WellSeparated
  assumption1 : S.Assumption1

end LimitedPriceChanges.AlgorithmI


