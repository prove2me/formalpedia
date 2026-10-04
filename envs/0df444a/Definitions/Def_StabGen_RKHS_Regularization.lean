-- Prove2me | Definitions.Def_StabGen_RKHS_Regularization
-- name    : StabGen_RKHS_Regularization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:37:55.76535+00:00
-- url     : https://prove2.me/theorems/18709786-fadb-4730-a336-4bbfed9ff189
-- title:
--   σ-admissibility and regularized objectives (19)–(20)
-- statement:
--   Let $F$ be a class of real-valued functions on $X$, and let $D_F$ be the set of all values $f(x)$ with $f\in F$ and $x\in X$. A cost $c(a,y)$ is **$\sigma$-admissible** with respect to $F$ when $\sigma\ge0$, $c(\cdot,y)$ is convex for every label $y$, and
--   $$|c(a,y)-c(b,y)|\le\sigma|a-b|\qquad(a,b\in D_F,\ y\in Y).$$
--
--   For a sample $S=(z_1,\ldots,z_m)$, an evaluation map $\operatorname{ev}(g,x)$, regularizer $N$ and weight $\lambda$, the full and truncated objectives are
--   $$R_r(g)=\frac1m\sum_{j=1}^m c(\operatorname{ev}(g,x_j),y_j)+\lambda N(g),\qquad R_r^{\setminus i}(g)=\frac1m\sum_{j\ne i}c(\operatorname{ev}(g,x_j),y_j)+\lambda N(g).$$
--
--   These definitions fix the loss and normalization used by Lemma 20 and Theorem 22.
--
--   **Formalization Note** The truncated sum retains $1/m$. The nonnegative requirement on $\sigma$ makes explicit its role as a Lipschitz constant even when $D_F$ has at most one point.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 512 (PDF p. 14), Definition 19 and Eqs. (19)–(20), https://jmlr.org/papers/v2/bousquet02a.html

import Mathlib
import Definitions.Def_FoundationsML_Stability_EmpiricalError

namespace StabGen.RKHS

open FoundationsML.Stability

/-- The range of predictions made by functions in `F`, denoted `D` in Definition 19. -/
def predictionDomain {X : Type*} (F : Set (X → ℝ)) : Set ℝ :=
  {a | ∃ f ∈ F, ∃ x : X, f x = a}

/-- Definition 19, p. 512: convexity of the cost in its prediction argument and a
uniform Lipschitz bound on the predictions attainable in `F`. A Lipschitz constant
is nonnegative, including when the prediction domain is a singleton or empty. -/
def SigmaAdmissible {X Y : Type*} (F : Set (X → ℝ))
    (c : ℝ → Y → ℝ) (σ : ℝ) : Prop :=
  0 ≤ σ ∧
  (∀ y : Y, ConvexOn ℝ Set.univ (fun a : ℝ => c a y)) ∧
  ∀ a ∈ predictionDomain F, ∀ b ∈ predictionDomain F, ∀ y : Y,
    |c a y - c b y| ≤ σ * |a - b|

/-- Equation (19): empirical loss with normalization `1/m`, plus regularization. -/
noncomputable def regRisk {X Y H : Type*} {m : ℕ} (c : ℝ → Y → ℝ)
    (ev : H → X → ℝ) (S : Fin m → X × Y) (lam : ℝ) (N : H → ℝ)
    (g : H) : ℝ :=
  EmpiricalError c S (ev g) + lam * N g

/-- Equation (20): remove observation `i` while retaining the normalization `1/m`. -/
noncomputable def truncRegRisk {X Y H : Type*} {m : ℕ} (c : ℝ → Y → ℝ)
    (ev : H → X → ℝ) (S : Fin m → X × Y) (i : Fin m)
    (lam : ℝ) (N : H → ℝ) (g : H) : ℝ :=
  (1 / (m : ℝ)) * ∑ j ∈ Finset.univ.erase i, Loss c (ev g) (S j) + lam * N g

end StabGen.RKHS


