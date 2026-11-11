-- Prove2me | Definitions.Def_IteratedLP_Gaussian_StrictInput
-- name    : IteratedLP_Gaussian_StrictInput
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:22:19.292227+00:00
-- url     : https://prove2.me/theorems/cab98555-73d3-40ec-9fe5-6995c15321f7
-- title:
--   Strict population histories (Definition 6.2), Section-6 inputs and compact input families
-- statement:
--   Fix a density $\alpha>0$, old margins $\kappa_1,\dots,\kappa_p$ and the new margin $\kappa_t$, $t=p+1$. A depth-$p$ population state $(q,\pi^{\mathrm{col}}_p,\pi^{\mathrm{row}}_p,\mu^{\mathrm{col}}_p)$, with $(X,R)\sim\pi^{\mathrm{col}}_p$, $(U,\Lambda)\sim\pi^{\mathrm{row}}_p$, $\bar X\sim\mu^{\mathrm{col}}_p$ and the moments of Algorithm 2, is a **strict population history** (Definition 6.2, $p\ge1$) if its three laws are probability laws with finite second moments and
--   1. $X\in(-1,1)^p$ and $\bar X\in[-1,1]^p$ almost surely; $\bar X_{r+1}=\bar X_r$ on $\{|\bar X_r|=1\}$ for $r<p$; $q=\mathbb P(|\bar X_p|<1)$ and $\mathrm{Law}(\bar X\mid|\bar X_p|<1)=\mathrm{Law}(X)$;
--   2. for every $r\le p$: $U_r\ge\kappa_r$, $\Lambda_r\ge0$, $\Lambda_r(U_r-\kappa_r)=0$ almost surely;
--   3. $q>0$, $Q^x\succ0$, $Q^\lambda\succ0$, $D^x=Q^x-Q^x_F\succ0$.
--
--   It is a **strict input** for round $t$ if $\Delta_t=\kappa_p-\kappa_t>0$. An input **satisfying the assumptions of Section 6** is the empty history ($p=0$, $q=1$, empty laws) when $(\alpha,\kappa_t)$ satisfies (1.2), or a strict input when $p\ge1$.
--
--   A family of inputs of fixed depth, density and margins is **compact** for the product of the Euclidean topology on $q$ and the $W_2$ topologies on the three laws.
--
--   These are the inputs of Lemma 6.4, Lemma 6.5 and Proposition 6.6.
--
--   **Formalization Note.** Finite second moments are integrability of $\|w_1\|^2+\|w_2\|^2$ (resp. $\|z\|^2$). The conditional law is `ProbabilityTheory.cond`. Compactness is sequential: every sequence in the family has a subsequence converging to a member for `inputDist` $=|q-q'|+W_2+W_2+W_2$; on $\mathbb R^p\times\mathbb R^p$ the $W_2$ uses Lean's product norm $\max(\|x\|,\|r\|)$, which is equivalent to the Euclidean norm on $\mathbb R^{2p}$ and so defines the same topology.
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 25, Definition 6.2; p. 23 (assumptions of Section 6); p. 27, Lemma 6.4; p. 34, after Definition 7.1 (compact families)

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Feasibility
import Definitions.Def_IteratedLP_Gaussian_StateEvolution

open MeasureTheory ProbabilityTheory Matrix

namespace IteratedLP.Gaussian

/-- A strict depth-`p` population history that is a strict input for round `t = p + 1`
(Definition 6.2, p. 25), for density `α`, old margins `κ_1, …, κ_p` (`κold`, 0-based) and new
margin `κ_t` (`κt`):
* `p ≥ 1`; the three laws are probability laws with finite second moments;
* (i) `X ∈ (-1,1)^p` and `X̄ ∈ [-1,1]^p` a.s.; `X̄_{r+1} = X̄_r` on `{|X̄_r| = 1}` for `r < p`;
  `q = P(|X̄_p| < 1)` and `Law(X̄ | |X̄_p| < 1) = Law(X)`;
* (ii) `U_r ≥ κ_r`, `Λ_r ≥ 0`, `Λ_r (U_r - κ_r) = 0` a.s. for every `r ≤ p`;
* (iii) `q > 0`, `Q^x ≻ 0`, `Q^λ ≻ 0`, `D^x = Q^x - Q^x_F ≻ 0`;
* strict input: `Δ_t = κ_p - κ_t > 0`. -/
structure IsStrictInput (α : ℝ) {p : ℕ} (κold : Fin p → ℝ) (κt : ℝ) (S : PopState p) :
    Prop where
  depth_pos : 0 < p
  prob_col : IsProbabilityMeasure S.πcol
  prob_row : IsProbabilityMeasure S.πrow
  prob_full : IsProbabilityMeasure S.μcol
  sq_col : Integrable (fun w => ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) S.πcol
  sq_row : Integrable (fun w => ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) S.πrow
  sq_full : Integrable (fun z => ‖z‖ ^ 2) S.μcol
  free_open : ∀ᵐ w ∂S.πcol, ∀ i, |w.1 i| < 1
  full_box : ∀ᵐ z ∂S.μcol, ∀ i, |z i| ≤ 1
  frozen_stay : ∀ᵐ z ∂S.μcol, ∀ (r : ℕ) (hr : r + 1 < p),
    |z ⟨r, by omega⟩| = 1 → z ⟨r + 1, hr⟩ = z ⟨r, by omega⟩
  q_eq : S.q = (S.μcol {z | |lastE z| < 1}).toReal
  free_law : cond S.μcol {z | |lastE z| < 1} = S.πcol.map Prod.fst
  row_kkt : ∀ᵐ w ∂S.πrow, ∀ r : Fin p,
    κold r ≤ w.1 r ∧ 0 ≤ w.2 r ∧ w.2 r * (w.1 r - κold r) = 0
  q_pos : 0 < S.q
  Qx_pd : (Qx S).PosDef
  Qlam_pd : (Qlam α S).PosDef
  Dx_pd : (Qx S - QxF S).PosDef
  margin_drop : κt < κold ⟨p - 1, by omega⟩

/-- An input for round `t = p + 1` satisfying the assumptions of Section 6 (p. 23): the empty
history at `p = 0` under the first-round feasibility condition (1.2) for `κ_1 = κt`, or a strict
input (Definition 6.2) when `p ≥ 1`. -/
def IsSectionSixInput (α : ℝ) {p : ℕ} (κold : Fin p → ℝ) (κt : ℝ) (S : PopState p) : Prop :=
  (p = 0 ∧ S.q = 1 ∧ S.πcol = Measure.dirac 0 ∧ S.πrow = Measure.dirac 0 ∧
    S.μcol = Measure.dirac 0 ∧ FirstRoundFeasible α κt) ∨
  IsStrictInput α κold κt S

/-- The distance between two inputs in the product of the Euclidean topology on `q` and the
`W₂` topologies on the three laws (Lemma 6.4, p. 27). -/
noncomputable def inputDist {p : ℕ} (S T : PopState p) : ENNReal :=
  ENNReal.ofReal |S.q - T.q| + W2 S.πcol T.πcol + W2 S.πrow T.πrow + W2 S.μcol T.μcol

/-- A family of inputs is compact for that topology, written sequentially: every sequence in
the family has a subsequence converging to a member of the family. -/
def IsCompactFamily {p : ℕ} (F : Set (PopState p)) : Prop :=
  ∀ u : ℕ → PopState p, (∀ n, u n ∈ F) →
    ∃ S ∈ F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => inputDist (u (φ n)) S) Filter.atTop (nhds 0)

end IteratedLP.Gaussian


