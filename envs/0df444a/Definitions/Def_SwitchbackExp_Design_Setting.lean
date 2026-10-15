-- Prove2me | Definitions.Def_SwitchbackExp_Design_Setting
-- name    : SwitchbackExp_Design_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:17.71665+00:00
-- url     : https://prove2.me/theorems/57a76ad9-9132-459f-a6a1-76d56c87dae9
-- title:
--   §3 and EC.3, pp. 11–13, ec3 — admissible outcomes 𝒴, minimax optimality (6), 𝕐±, f^m_𝕋(t), O_𝕋(t,t′), the error term (EC.2), t_k, the objective (7) and 𝕋*
-- statement:
--   This file adds the objects of §3 and of the e-companion EC.3 on top of the switchback model.
--
--   1. **Admissible outcomes.** $\mathcal Y$ is the set of potential outcomes satisfying Assumptions 1–3 with bound $B$.
--   2. **Fair coins.** $q\equiv1/2$.
--   3. **Minimax optimality (6).** A regular design $(\mathbb T,\mathbb Q)$ solves
--   $$\min_{\mathbb T\subseteq[T],\,\mathbb Q}\ \max_{\mathbb Y\in\mathcal Y}\ r(\eta_{\mathbb T,\mathbb Q},\mathbb Y)$$
--   if for every regular design $(\mathbb T',\mathbb Q')$ and every $\mathbb Y\in\mathcal Y$ there is $\mathbb Y'\in\mathcal Y$ with $r(\eta_{\mathbb T,\mathbb Q},\mathbb Y)\le r(\eta_{\mathbb T',\mathbb Q'},\mathbb Y')$; that is, its worst-case risk is at most the worst-case risk of every regular design.
--   4. **Extreme outcomes** (p. 12). $\mathbb Y^+$ has every outcome equal to $B$ and $\mathbb Y^-$ every outcome equal to $-B$; in particular $Y_t(\mathbf 1_{m+1})=Y_t(\mathbf 0_{m+1})=\pm B$.
--   5. **Determining and overlapping points** (p. ec3). $f^m_{\mathbb T}(t)=\{f_{\mathbb T}(i):t-m\le i\le t\}$, with $J=|f^m_{\mathbb T}(t)|$, and $O_{\mathbb T}(t,t')=f^m_{\mathbb T}(t)\cap f^m_{\mathbb T}(t')$, with $J^o=|O_{\mathbb T}(t,t')|$.
--   6. **Error term** (EC.2). For $t\in\{m+1,\dots,T\}$,
--   $$\mathbb 1_t=Y_t(\mathbf 1_{m+1})\Bigl[\mathbf 1\{W_{t-m:t}=\mathbf 1_{m+1}\}\prod_{u\in f^m_{\mathbb T}(t)}\frac1{q_u}-1\Bigr]-Y_t(\mathbf 0_{m+1})\Bigl[\mathbf 1\{W_{t-m:t}=\mathbf 0_{m+1}\}\prod_{u\in f^m_{\mathbb T}(t)}\frac1{\bar q_u}-1\Bigr],$$
--   so that $\hat\tau_m-\tau_m=\frac1{T-m}\sum_{t=m+1}^T\mathbb 1_t$.
--   7. **Indexing.** $t_k$ is the $k$-th smallest point of $\mathbb T$ ($k=0,\dots,K$, $K=|\mathbb T|-1$), and $t_{K+1}=T+1$.
--   8. **The subset selection objective (7).**
--   $$4\sum_{k=0}^{K}(t_{k+1}-t_k)^2+8m(t_K-t_1)+4m^2K-4m^2+4\sum_{k=1}^{K-1}\bigl[(m-t_{k+1}+t_k)^+\bigr]^2,$$
--   with $(a)^+=\max\{a,0\}$.
--   9. **The optimal design of Theorem 2.** $\mathbb T^*=\{1,2m+1,3m+1,\dots,(n-2)m+1\}$.
--
--   **Formalization Note** Minimax optimality is stated in the $\forall\exists$ form above rather than through a supremum, so no junk value of a supremum is ever involved; by Lemma 1 the worst case is attained, so this is the page's min–max. $t_k$ is computed from the order embedding of the finite set and returns $T+1$ for every index beyond $K$; statements only read $t_0,\dots,t_{K+1}$. In the objective (7) the sums run over $k\in\{0,\dots,K\}$ and $k\in\{1,\dots,K-1\}$, the latter empty at $K=1$, as on the page. $\mathbb Y^\pm$ are the constant outcome functions; the page fixes only $Y_t(\mathbf 1_{m+1})$ and $Y_t(\mathbf 0_{m+1})$, and the constant functions are the admissible members with those values.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), §3 pp. 11–13, (6), Assumption 3, 𝕐± (p. 12), (7) (p. 13); EC.3.1 p. ec3, (EC.2)

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model

namespace SwitchbackExp.Design

open Finset

/-- The admissible potential outcomes `𝒴` of §3 (pp. 6, 12): Assumptions 1–3. -/
def Admissible (m T : ℕ) (B : ℝ) (Y : Outcomes) : Prop :=
  NonAnticipating T Y ∧ Carryover m T Y ∧ Bounded B T Y

/-- Fair coins: `q_k = 1/2` at every randomization point. -/
noncomputable def half : ℕ → ℝ := fun _ => 1 / 2

/-- `(𝕋, ℚ)` solves the minimax problem (6) (p. 11): it is a regular design, and for every regular
design `(𝕋′, ℚ′)` and every admissible `𝕐` there is an admissible `𝕐′` with
`r(η_{𝕋,ℚ}, 𝕐) ≤ r(η_{𝕋′,ℚ′}, 𝕐′)`, i.e. its worst-case risk is at most that of every regular design. -/
def IsMinimaxOptimal (m T : ℕ) (B : ℝ) (P : Finset ℕ) (q : ℕ → ℝ) : Prop :=
  IsRegularPoints T P ∧ IsRegularProbs P q ∧
    ∀ P' q', IsRegularPoints T P' → IsRegularProbs P' q' →
      ∀ Y, Admissible m T B Y → ∃ Y', Admissible m T B Y' ∧ risk m T P q Y ≤ risk m T P' q' Y'

/-- `𝕐⁺` (p. 12): every potential outcome equals `B`, so `Y_t(1_{m+1}) = Y_t(0_{m+1}) = B`. -/
def Yplus (B : ℝ) : Outcomes := fun _ _ => B

/-- `𝕐⁻` (p. 12): every potential outcome equals `−B`, so `Y_t(1_{m+1}) = Y_t(0_{m+1}) = −B`. -/
def Yminus (B : ℝ) : Outcomes := fun _ _ => -B

/-- `f^m_𝕋(t) = {f_𝕋(i) : i ∈ {t−m, …, t}}` (EC.3.1, p. ec3), the determining randomization points of
periods `t−m, …, t`. Its cardinality is the paper's `J`. -/
def detPoints (P : Finset ℕ) (m t : ℕ) : Finset ℕ :=
  (Finset.Icc (t - m) t).image (detPoint P)

/-- `O_𝕋(t, t′) = f^m_𝕋(t) ∩ f^m_𝕋(t′)` (EC.3.1, p. ec3). Its cardinality is the paper's `J^o`. -/
def overlap (P : Finset ℕ) (m t t' : ℕ) : Finset ℕ :=
  detPoints P m t ∩ detPoints P m t'

/-- The error term `𝟙_t(𝕋, ℚ, 𝕐)` of (EC.2) (p. ec3), evaluated on the path `w`. -/
noncomputable def errTerm (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (t : ℕ) (w : Path) : ℝ :=
  Y1 Y t * (onesInd m w t * ∏ u ∈ detPoints P m t, 1 / q u - 1)
    - Y0 Y t * (zerosInd m w t * ∏ u ∈ detPoints P m t, 1 / (1 - q u) - 1)

/-- The `k`-th randomization point `t_k` of `𝕋 = {t₀ = 1 < t₁ < … < t_K}` (0-based, `K = |𝕋| − 1`),
with the paper's convention `t_{K+1} = T + 1` (p. 8); `T + 1` is also returned for `k > K + 1`,
which no statement reads. -/
def tpt (P : Finset ℕ) (T k : ℕ) : ℕ :=
  if h : k < P.card then P.orderEmbOfFin rfl ⟨k, h⟩ else T + 1

/-- The objective of the subset selection problem (7) (p. 13), with `K = |𝕋| − 1`:
`4 ∑_{k=0}^{K} (t_{k+1} − t_k)² + 8m(t_K − t_1) + 4m²K − 4m² + 4 ∑_{k=1}^{K−1} [(m − t_{k+1} + t_k)⁺]²`. -/
noncomputable def objective7 (m T : ℕ) (P : Finset ℕ) : ℝ :=
  let K := P.card - 1
  4 * ∑ k ∈ Finset.range (K + 1), ((tpt P T (k + 1) : ℝ) - tpt P T k) ^ 2
    + 8 * m * ((tpt P T K : ℝ) - tpt P T 1) + 4 * (m : ℝ) ^ 2 * K - 4 * (m : ℝ) ^ 2
    + 4 * ∑ k ∈ Finset.Icc 1 (K - 1), (max ((m : ℝ) - tpt P T (k + 1) + tpt P T k) 0) ^ 2

/-- The design of Theorem 2 (p. 13): `𝕋* = {1, 2m+1, 3m+1, …, (n−2)m+1}`. -/
def optPoints (m n : ℕ) : Finset ℕ :=
  insert 1 ((Finset.Icc 2 (n - 2)).image (fun k => k * m + 1))

end SwitchbackExp.Design


