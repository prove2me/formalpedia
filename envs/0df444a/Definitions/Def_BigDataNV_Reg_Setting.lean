-- Prove2me | Definitions.Def_BigDataNV_Reg_Setting
-- name    : BigDataNV_Reg_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:27:41.648997+00:00
-- url     : https://prove2.me/theorems/49004bb5-0cf3-4d07-b402-e22b5bb4ad05
-- title:
--   §2–§3, pp. 5–9, App. B p. 27 — newsvendor cost C, linear rules, (NV-reg) and its leave-one-out objective, the support X × [0, D̄]
-- statement:
--   This file fixes the objects of the feature-based newsvendor model of Rudin and Vahn on which the generalization bound for the regularized algorithm (NV-reg) is stated.
--
--   1. **Newsvendor cost** (display (2), p. 5). For unit backordering cost $b$ and unit holding cost $h$, the cost of ordering $q$ when demand is $d$ is
--   $$C(q;d)=b\,(d-q)^+ + h\,(q-d)^+ .$$
--   2. **Linear decision rules** (§2.3, p. 6). Features are vectors $x\in\mathbb R^p$, and a vector $q\in\mathbb R^p$ acts as the rule $q(x)=q^\top x=\sum_{j=1}^p q^j x^j$.
--   3. **The (NV-reg) objective** (§2.5, p. 7). For a sample $S_n=\{(x_i,d_i)\}_{i=1}^n$ and a regularization parameter $\lambda$,
--   $$\hat R(q;S_n)+\lambda\|q\|_2^2=\frac1n\sum_{i=1}^n C(q^\top x_i;d_i)+\lambda\|q\|_2^2 ,$$
--   and $q$ is an **(NV-reg) solution** if it minimizes this objective over all $q\in\mathbb R^p$.
--   4. **The leave-one-out objective** used by the stability argument of Appendix B (Theorems 4 and 5): for an index $i$,
--   $$\frac1n\sum_{j\ne i} C(q^\top x_j;d_j)+\lambda\|q\|_2^2 ,$$
--   with the weight $1/n$ kept, and a **leave-one-out solution** is a minimizer of it over $\mathbb R^p$.
--   5. **The data support** (§3, p. 9). For a feature domain $\mathcal X\subseteq\mathbb R^p$ and a demand cap $\bar D$, the support of the data is $\mathcal X\times\mathcal D$ with $\mathcal D=[0,\bar D]$.
--
--   The empirical risk $\hat R$ and the true risk $R_{true}(q)=\mathbb E_{x,d}[C(q(x);d)]$ are the published empirical and generalization errors, and the objective and its leave-one-out version are the published regularized objectives (19)–(20) of Bousquet and Elisseeff, specialized to the newsvendor cost and the linear evaluation $q(x)=\langle q,x\rangle$.
--
--   **Formalization Note** $C(q;d)$ is the published newsboy loss with overage cost $h$ and underage cost $b$. The regularizer is the squared norm $\lambda\|q\|_2^2$: display (NV-reg) prints $\lambda\|q\|_2^2$ on its left-hand side and $\lambda\|q\|_2$ in the middle, and the text calls the problem a quadratic program, so the squared form is taken. The intercept convention $x^1=1$ of §2.3 is not built in; it is the special case of a feature domain inside $\{x : x^1=1\}$.
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), pp. 5–9 and 27–31, display (2), §2.3, display (NV-reg), §3, App. B

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_RKHS_Regularization

namespace BigDataNV.Reg

/-- The newsvendor cost (2), p. 5: `C(q; d) = b (d − q)⁺ + h (q − d)⁺`, with unit backordering
cost `b` and unit holding cost `h`. It is the published `newsboyLoss` with overage cost `co = h`
and underage cost `cu = b`. -/
noncomputable def nvCost (b h : ℝ) : ℝ → ℝ → ℝ :=
  fun q d => InventoryControl.newsboyLoss h b q d

/-- A linear decision rule, §2.3, p. 6: the vector `q ∈ ℝᵖ` acts on a feature vector `x` by
`q(x) = qᵀx = ∑ⱼ qʲ xʲ`. -/
noncomputable def linEval {p : ℕ} : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → ℝ :=
  fun g x => inner ℝ g x

/-- The objective of (NV-reg), §2.5, p. 7: `R̂(q; Sₙ) + λ‖q‖₂²`. -/
noncomputable def nvRegObjective {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (q : EuclideanSpace ℝ (Fin p)) : ℝ :=
  StabGen.RKHS.regRisk (nvCost b h) linEval S lam (fun g => ‖g‖ ^ 2) q

/-- `q` solves (NV-reg) on the sample `S`: it minimizes `R̂(·; Sₙ) + λ‖·‖₂²` over all of `ℝᵖ`. -/
def IsNVRegSolution {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (q : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin p), nvRegObjective b h lam S q ≤ nvRegObjective b h lam S g

/-- The leave-one-out objective of the stability argument (App. B, Theorems 4 and 5): the `i`-th
data term is dropped and the weight `1/n` is kept,
`(1/n) ∑_{j ≠ i} C(qᵀxⱼ; dⱼ) + λ‖q‖₂²`. -/
noncomputable def nvRegLooObjective {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (i : Fin n) (q : EuclideanSpace ℝ (Fin p)) : ℝ :=
  StabGen.RKHS.truncRegRisk (nvCost b h) linEval S i lam (fun g => ‖g‖ ^ 2) q

/-- `q` minimizes the leave-one-out objective `nvRegLooObjective b h lam S i` over `ℝᵖ`. -/
def IsNVRegLooSolution {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (i : Fin n) (q : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin p), nvRegLooObjective b h lam S i q ≤ nvRegLooObjective b h lam S i g

/-- The data support `X × D` of §3, p. 9, with `D = [0, D̄]`. -/
def dataSupport {p : ℕ} (Xdom : Set (EuclideanSpace ℝ (Fin p))) (Dbar : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × ℝ) :=
  Xdom ×ˢ Set.Icc 0 Dbar

end BigDataNV.Reg


