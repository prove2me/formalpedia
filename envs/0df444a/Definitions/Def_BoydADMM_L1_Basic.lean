-- Prove2me | Definitions.Def_BoydADMM_L1_Basic
-- name    : BoydADMM_L1_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:58.434718+00:00
-- url     : https://prove2.me/theorems/36c770ac-04b0-43a7-a6c5-9a9a647625c0
-- title:
--   Unique minimizers, the Huber penalty and vector soft thresholding (Chapter 6)
-- statement:
--   These are the scalar and vector objects used by the closed-form ADMM updates of Chapter 6.
--
--   1. **Unique minimizer.** For a real function $F$ on a set $\alpha$ and $s\subseteq\alpha$, a point $x$ is the unique minimizer of $F$ over $s$ if $x\in s$, $F(x)\le F(y)$ for every $y\in s$, and every $y\in s$ with $F(y)\le F(x)$ equals $x$. This is how an update written as $x^{k+1} := \operatorname{argmin}_{y\in s} F(y)$, and then given by a single formula, is read.
--   2. **Soft thresholding** (§4.4.3, p. 32), used by the updates below, is the shared definition `BoydADMM.Prox.softThreshold` (imported, not redefined here). For $\kappa,a\in\mathbb R$,
--   $$S_\kappa(a)=\begin{cases}a-\kappa & a>\kappa,\\ 0 & |a|\le\kappa,\\ a+\kappa & a<-\kappa.\end{cases}$$
--   3. **Huber penalty** (§6.1.1, p. 40). For scalar $a$,
--   $$g^{\mathrm{hub}}(a)=\begin{cases}a^2/2 & |a|\le 1,\\ |a|-1/2 & |a|>1,\end{cases}$$
--   and for $z\in\mathbb R^m$, $g^{\mathrm{hub}}(z)=\sum_{i=1}^m g^{\mathrm{hub}}(z_i)$.
--   4. **Vector soft thresholding** (§6.4.2, p. 45). For $\kappa\in\mathbb R$ and $a\in\mathbb R^m$,
--   $$\mathcal S_\kappa(a)=\bigl(1-\kappa/\|a\|_2\bigr)_+\,a,\qquad \mathcal S_\kappa(0)=0 .$$
--
--   Soft thresholding is the proximity operator of the $\ell_1$ norm and vector soft thresholding that of the Euclidean norm; the Huber penalty interpolates between least squares and least absolute deviations.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin m)`, so $\|\cdot\|$ is the Euclidean norm. $(t)_+$ is `max t 0`. The case $a=0$ of $\mathcal S_\kappa$ is an explicit branch, as the book states it. $S_\kappa$ is written in the book's three-case form; its equivalent closed forms are not definitions.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 32 (§4.4.3, soft thresholding); p. 40 (§6.1.1, Huber penalty); p. 45 (§6.4.2, vector soft thresholding)

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

namespace BoydADMM.L1

/-! Objects of Chapter 6 (ℓ1-norm problems) of Boyd–Parikh–Chu–Peleato–Eckstein (2011),
pp. 38–45. Vectors live in `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm `‖·‖₂`. -/

/-- `x` is the unique minimizer of `F` over `s`: `x ∈ s`, `F x ≤ F y` for every `y ∈ s`, and
every `y ∈ s` with `F y ≤ F x` equals `x`. This is how "`x := argmin_{y ∈ s} F(y)`" is read when
the book writes the minimizer as a single formula. -/
def IsUniqueMinimizerOn {α : Type*} (F : α → ℝ) (s : Set α) (x : α) : Prop :=
  x ∈ s ∧ (∀ y ∈ s, F x ≤ F y) ∧ ∀ y ∈ s, F y ≤ F x → y = x

/-- The scalar Huber penalty `g^hub(a)` (§6.1.1, p. 40): `a²/2` if `|a| ≤ 1`, `|a| − 1/2` if
`|a| > 1`. -/
noncomputable def huber (a : ℝ) : ℝ :=
  if |a| ≤ 1 then a ^ 2 / 2 else |a| - 1 / 2

/-- The Huber penalty of a vector, the sum of the Huber penalties of its components (p. 40). -/
noncomputable def huberVec {m : ℕ} (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, huber (z i)

/-- The vector soft thresholding operator `S_κ : ℝᵐ → ℝᵐ` (§6.4.2, p. 45):
`S_κ(a) = (1 − κ/‖a‖₂)₊ a`, with `S_κ(0) = 0`. -/
noncomputable def blockSoftThreshold {m : ℕ} (κ : ℝ) (a : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  if a = 0 then 0 else max (1 - κ / ‖a‖) 0 • a

end BoydADMM.L1


