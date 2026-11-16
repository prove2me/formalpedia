-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_csp
-- name    : HindsightGain_Uniform_Supplement_csp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:50:39.281232+00:00
-- url     : https://prove2.me/theorems/531535ff-b6fd-42c1-9646-220f560ed5ce
-- title:
--   Max-rCSPs with varying alphabets, centered energy and the estimator Est_q
-- statement:
--   Fix $r\ge2$. A Max-rCSP on $n$ variables has a nonempty finite alphabet $A_i$ for each variable $i$ and one real payoff table $g_e:\prod_{i\in e}A_i\to\mathbb R$ for each $r$-element set $e\subseteq[n]$ (an absent constraint is the zero table). For $S\subseteq[n]$ and $p\in[0,1]^n$,
--   $$\mathrm{Opt}_g(S)=\max_{x}\sum_{e\subseteq S}g_e(x_e),\qquad \mathrm{Opt}_{g,p}=\max_x\sum_e\Big(\prod_{i\in e}p_i\Big)g_e(x_e),$$
--   with $\mathrm{Opt}_g=\mathrm{Opt}_g([n])$ and $\mathrm{Opt}_g(S)=0$ when $|S|<r$. Let $\bar g_e$ be the average of all entries of $g_e$; the **centered energy** is
--   $$\mathcal E(g)^2=\sum_e\sum_{a}\big(g_e(a)-\bar g_e\big)^2,$$
--   and for weights $w$ put $Q(w)=\sum_e w_e^2$.
--
--   The estimator $\mathsf{Est}_q$ ($1\le q\le n$ real) samples $S=S_{q/n}$; if $|S|>4q$ it outputs $0$, otherwise it reads every table $g_e$ with $e\subseteq S$ and outputs $(q/n)^{-r}\mathrm{Opt}_g(S)$. The number of tables read is $0$ after the cutoff and $\binom{|S|}{r}$ otherwise.
--
--   These objects are the CSP interface of Section 5.
--
--   **Formalization Note** Alphabets are `Fin (k i)` with `k i ≥ 1`; tables are indexed by labelings of the variables of $e$. $\mathrm{Opt}_g(S)$ is the maximum over labelings of all variables, which equals the maximum over labelings of $S$ since only constraints inside $S$ count.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §5.1 pp.22-23 eqs. (28)-(29), §5.3 p.25

import Mathlib
import Definitions.Def_HindsightGain_Uniform_model
import Definitions.Def_HindsightGain_Uniform_Supplement_subsets

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- A Max-rCSP (§5.1, p.22): variable `i` has the nonempty finite alphabet `Fin (k i)`, and every
unordered `r`-set `e` carries an arbitrary real payoff table on the labels of its variables
(an absent constraint is the zero table). -/
structure CSP (n r : ℕ) where
  k : Fin n → ℕ
  k_pos : ∀ i, 1 ≤ k i
  g : (e : Edge n r) → ((i : {i // i ∈ e.val}) → Fin (k i)) → ℝ

/-- `Opt_g(S)`: the maximum over labelings of the payoff of the constraints inside `S`. Labels
outside `S` do not affect the sum, so this is the maximum over labelings of `S`; it is `0` when
`|S| < r`. -/
def optOn {n r : ℕ} (g : CSP n r) (S : Finset (Fin n)) : ℝ :=
  ⨆ x : (i : Fin n) → Fin (g.k i),
    ∑ e ∈ (Finset.univ : Finset (Edge n r)).filter (fun e => e.val ⊆ S), g.g e (fun i => x i)

/-- `Opt_g = Opt_g([n])`. -/
def opt {n r : ℕ} (g : CSP n r) : ℝ := optOn g Finset.univ

/-- `Opt_{g,p}`: the optimum of the mean objective, each constraint weighted by `∏_{i∈e} p_i`. -/
def optWeighted {n r : ℕ} (g : CSP n r) (p : Fin n → ℝ) : ℝ :=
  ⨆ x : (i : Fin n) → Fin (g.k i), ∑ e : Edge n r, (∏ i ∈ e.val, p i) * g.g e (fun i => x i)

/-- `ḡ_e`, the uniform average of all entries of table `e`. -/
def tableMean {n r : ℕ} (g : CSP n r) (e : Edge n r) : ℝ :=
  (∑ a : (i : {i // i ∈ e.val}) → Fin (g.k i), g.g e a) /
    (Fintype.card ((i : {i // i ∈ e.val}) → Fin (g.k i)) : ℝ)

/-- Equation (28): the centered energy `E(g)`. -/
def energy {n r : ℕ} (g : CSP n r) : ℝ :=
  Real.sqrt (∑ e : Edge n r, ∑ a : (i : {i // i ∈ e.val}) → Fin (g.k i),
    (g.g e a - tableMean g e) ^ 2)

/-- `Q(w) = Σ_e w_e²` (p.23). -/
def Qw {n r : ℕ} (w : Edge n r → ℝ) : ℝ := ∑ e : Edge n r, (w e) ^ 2

/-- Estimator `Est_q` (p.25), as a function of the sampled set `S = S_{q/n}`:
output `0` if `|S| > 4q`, otherwise `(q/n)^{-r} Opt_g(S)`. -/
def estimator {n r : ℕ} (g : CSP n r) (q : ℝ) (S : Finset (Fin n)) : ℝ :=
  if 4 * q < (S.card : ℝ) then 0 else ((q / n) ^ r)⁻¹ * optOn g S

/-- Number of payoff tables `Est_q` reads on the sample `S`: none after the cutoff, otherwise
every table `g_e` with `e ⊆ S`. -/
def tablesRead (n r : ℕ) (q : ℝ) (S : Finset (Fin n)) : ℕ :=
  if 4 * q < (S.card : ℝ) then 0 else S.card.choose r

end HindsightGain.Uniform.Supplement


