-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
-- name    : BilevelSOC_SecondOrder_Supplement_Multipliers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:34:55.84578+00:00
-- url     : https://prove2.me/theorems/77209bce-4963-4cd6-ae17-c31e078effd8
-- title:
--   §3, Assumptions 4.10 and 4.14 — lower multipliers, scoped convexity and systems (4.6)–(4.7)
-- statement:
--   Let $D=(F,f,G,g)$ be the published bilevel data, let $z=(x,y)$, and let $\lambda\in\mathbb R^q$. The lower Lagrangian and multiplier set are
--
--   $$L(z,\lambda)=f(z)+\sum_i\lambda_i g_i(z),\quad \Lambda(z)=\{\lambda:\nabla_y L(z,\lambda)=0,\ \lambda\ge0,\ \lambda^Tg(z)=0\}.$$
--
--   The partial gradient is the gradient of the $y$ section, and its derivative in a joint direction $d$ is $\nabla^2_{yx}h(z)d_x+\nabla^2_{yy}h(z)d_y$. LMFCQ requires a strictly decreasing $y$ direction for every active lower inequality. Local boundedness concerns the entire lower feasible map $K$, uniformly on a neighborhood, with no compactness imposed away from that neighborhood. The lower linearization cone uses only active lower $y$ derivatives.
--
--   `FixedConvexLower` is Assumption 4.10: convex lower objective sections, and lower constraints independent of $x$ and convex in $y$. `ConvexKKTExact` carries the convexity of Assumption 4.14 together with its explicitly stated KKT-equivalence consequence: $y\in S(x)$ iff $y\in K(x)$ and $\Lambda(x,y)\ne\varnothing$. It imposes no chosen stronger named CQ. The abnormal-multiplier condition is the full implication (4.6), for every nonzero lower linearized direction and every multiplier. The variational system contains (4.1a,b) and every line of (4.7), with independent nonnegative $\lambda,\mu$ and unrestricted $\kappa\in\mathbb R$.
--
--   These definitions share the lower optimality objects across the variational and KKT companion theorems. **Formalization Note** The exact KKT consequence weakens the unspecified CQ in Assumption 4.14; this generalization is used only in Lemma 4.15 and Theorem 4.18. All differentiations in theorems are protected by the published standing $C^2$ assumption.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 3–4, 6–10, 12–17, §3, Assumptions 4.10 and 4.14

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Model
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
variable {n m p q : ℕ}
noncomputable def yGrad (h : E n × Y m → ℝ) (z : E n × Y m) : Y m :=
  gradient (fun y => h (z.1, y)) z.2
noncomputable def yHess (h : E n × Y m → ℝ) (z d : E n × Y m) : Y m :=
  fderiv ℝ (yGrad h) z d
noncomputable def lagrangian (D : Data n m p q) (lam : Fin q → ℝ)
    (z : E n × Y m) : ℝ := D.f z + ∑ i, lam i * D.g i z
noncomputable def multipliers (D : Data n m p q) (z : E n × Y m) : Set (Fin q → ℝ) :=
  {lam | yGrad (lagrangian D lam) z = 0 ∧ (∀ i, 0 ≤ lam i) ∧
    (∑ i, lam i * D.g i z) = 0}
def LMFCQ (D : Data n m p q) (z : E n × Y m) : Prop :=
  ∃ v : Y m, ∀ i ∈ actg D z, fderiv ℝ (D.g i) z (0, v) < 0
def LowerLocallyBounded (D : Data n m p q) (x : E n) : Prop :=
  ∃ U ∈ 𝓝 x, ∃ B : Set (Y m), Bornology.IsBounded B ∧
    ∀ a ∈ U, lowerFeas D a ⊆ B
/-- Exactly Assumption 4.10, with independence expressed by equality of functions. -/
def FixedConvexLower (D : Data n m p q) : Prop :=
  (∀ x, ConvexOn ℝ Set.univ (fun y => D.f (x, y))) ∧
    (∀ i x y, D.g i (x, y) = D.g i (0, y)) ∧
    ∀ i, ConvexOn ℝ Set.univ (fun y => D.g i (0, y))
/-- Convexity and the exact consequence of the CQ in Assumption 4.14. -/
def ConvexKKTExact (D : Data n m p q) : Prop :=
  (∀ x, ConvexOn ℝ Set.univ (fun y => D.f (x, y))) ∧
  (∀ i x, ConvexOn ℝ Set.univ (fun y => D.g i (x, y))) ∧
  ∀ x y, y ∈ solMap D x ↔ y ∈ lowerFeas D x ∧ (multipliers D (x, y)).Nonempty
def lowerLinCone (D : Data n m p q) (z : E n × Y m) : Set (Y m) :=
  {u | ∀ i ∈ actg D z, fderiv ℝ (D.g i) z (0, u) ≤ 0}
noncomputable def abnormalCondition (D : Data n m p q) (z : E n × Y m) : Prop :=
  ∀ u ∈ lowerLinCone D z, u ≠ 0 → ∀ lam : Fin q → ℝ,
    (∑ i, lam i • yGrad (D.g i) z) = 0 → (∀ i, 0 ≤ lam i) →
    (∑ i, lam i * D.g i z) = 0 →
    0 ≤ (∑ i, lam i * fderiv ℝ (fderiv ℝ (D.g i)) z (0, u) (0, u)) → lam = 0
noncomputable def variationalSystem (D : Data n m p q) (z d : E n × Y m)
    (lam : Fin q → ℝ) (κ : ℝ) (μ : Fin q → ℝ) : Prop :=
  fderiv ℝ D.F z d ≤ 0 ∧
  (∀ i ∈ actG D z, fderiv ℝ (D.G i) z d ≤ 0) ∧
  yHess D.f z d + κ • yGrad D.f z +
    (∑ i, (lam i • yHess (D.g i) z (0, d.2) + μ i • yGrad (D.g i) z)) = 0 ∧
  yGrad D.f z + (∑ i, lam i • yGrad (D.g i) z) = 0 ∧
  (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i * D.g i z) = 0 ∧
  (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i * D.g i z) = 0 ∧
  (∑ i, μ i * fderiv ℝ (D.g i) z (0, d.2)) = 0 ∧
  d.2 ∈ lowerLinCone D z ∧ fderiv ℝ D.f z (0, d.2) = 0
end BilevelSOC.SecondOrder.Supplement


