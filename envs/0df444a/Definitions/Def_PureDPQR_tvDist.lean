-- Prove2me | Definitions.Def_PureDPQR_tvDist
-- name    : PureDPQR_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:52.071918+00:00
-- url     : https://prove2.me/theorems/f6a6ba23-6dbc-4606-9075-5cb1c846155f
-- title:
--   Finite laws: total variation distance, couplings, relative entropy
-- statement:
--   A law on a finite set $Y$ is a function $P:Y\to[0,1]$ with $\sum_yP(y)=1$; $P(F)=\sum_{y\in F}P(y)$. The **total variation distance** is
--
--   $$\|P-Q\|_{\mathrm{TV}}=\frac12\sum_{y\in Y}|P(y)-Q(y)| .$$
--
--   A **coupling** of $P$ and $Q$ is a law $\mu$ on $Y\times Y$ with marginals $P$ and $Q$ (the joint law of a pair $(X,Y)$ with $X\sim P$, $Y\sim Q$). For probability vectors $p,q\in\Delta_m$ with all $q_j>0$, the **relative entropy** is
--
--   $$\mathrm{KL}(p\|q)=\sum_{j:\,p_j>0}p_j\log\frac{p_j}{q_j}.$$
--
--   These are the tools of Lemmas 12, 13 and 14.
--
--   **Formalization Note** Laws are real functions on a `Fintype`; probability vectors are functions `Fin m → ℝ`.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), §3.2, p.14 (PDF p.15)

import Mathlib

namespace PureDPQR

/-!
# Finite laws: total variation, couplings, relative entropy

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), §3.2, p.14 (PDF p.15).

**Formalization Note.** A law on a finite set `Y` is a function `P : Y → ℝ` with nonnegative
values summing to `1` (`IsPMF`); `P(F) = ∑_{y ∈ F} P(y)`. A coupling of `P` and `Q` is a law on
`Y × Y` with marginals `P` and `Q`. Probability vectors in `Δ_m` are functions `Fin m → ℝ`.
-/

/-- `P : Y → ℝ` is a law on the finite set `Y`: nonnegative values summing to `1`. -/
def IsPMF {Y : Type*} [Fintype Y] (P : Y → ℝ) : Prop :=
  (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1

/-- Total variation distance of laws on a finite set (p.14):
`‖P − Q‖_TV = (1/2) ∑_{y ∈ Y} |P(y) − Q(y)|`. -/
noncomputable def tvDist {Y : Type*} [Fintype Y] (P Q : Y → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |P y - Q y|

/-- `μ` is a coupling of the finite laws `P` and `Q`: a law on `Y × Y` whose first marginal is `P`
and whose second marginal is `Q`, i.e. the joint law of a pair `(X, Y)` with `X ∼ P`, `Y ∼ Q`. -/
def IsCoupling {Y : Type*} [Fintype Y] (P Q : Y → ℝ) (μ : Y × Y → ℝ) : Prop :=
  (∀ z, 0 ≤ μ z) ∧ (∀ x, ∑ y, μ (x, y) = P x) ∧ (∀ y, ∑ x, μ (x, y) = Q y)

/-- Relative entropy of probability vectors (p.14): `KL(p‖q) = ∑_{j : p_j > 0} p_j log(p_j/q_j)`. -/
noncomputable def kl {m : ℕ} (p q : Fin m → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), p j * Real.log (p j / q j)

end PureDPQR


