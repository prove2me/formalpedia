-- Prove2me | Definitions.Def_CorrWardrop_Lagrangian
-- name    : CorrWardrop_Lagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:22.314828+00:00
-- url     : https://prove2.me/theorems/2bb1bb60-bfe5-4406-9c78-9379a47a642c
-- title:
--   KKT conditions, Lagrangian and its saddle points, supports and the relative interior of WE(Γ) (proof of Proposition 4)
-- statement:
--   These are the objects used in the second half of the proof of Proposition 4, for the convex program
--   $$
--   \min\Big\{\Phi(y):\ \sum_{a\in\mathcal A^k}y^k_a=\gamma^k\ \forall k,\quad y^k_a\ge 0\ \forall k,a\Big\}.
--   $$
--
--   1. **Multipliers.** $\lambda=\big((\lambda^k)_{k\in\mathcal K},(\lambda^k_a)_{k\in\mathcal K,a\in\mathcal A^k}\big)$, with $\lambda^k$ attached to the equality constraint of population $k$ and $\lambda^k_a$ to the sign constraint on $y^k_a$.
--   2. **KKT conditions.** $(\hat y,\hat\lambda)$ satisfies the KKT conditions if, for all $k$ and $a\in\mathcal A^k$,
--   $$
--   \frac{\partial\Phi}{\partial y^k_a}(\hat y)=\hat\lambda^k+\hat\lambda^k_a,\qquad \hat\lambda^k_a\,\hat y^k_a=0,\qquad\hat\lambda^k_a\ge 0,\qquad \sum_{a\in\mathcal A^k}\hat y^k_a=\gamma^k .
--   $$
--   3. **Lagrangian.**
--   $$
--   \mathcal L(y,\lambda)=\Phi(y)-\sum_{k}\lambda^k\Big(\sum_{a\in\mathcal A^k}y^k_a-\gamma^k\Big)-\sum_k\sum_{a\in\mathcal A^k}\lambda^k_a\,y^k_a .
--   $$
--   4. **Saddle point.** Given a set $U$ of flow vectors (the domain of $\Phi$), $(\hat y,\hat\lambda)$ is a saddle point if $\hat y\in U$, $\hat\lambda^k_a\ge0$ for all $k,a$, and for every $y\in U$ and every $\lambda$ with $\lambda^k_a\ge0$,
--   $$
--   \mathcal L(\hat y,\lambda)\le\mathcal L(\hat y,\hat\lambda)\le\mathcal L(y,\hat\lambda).
--   $$
--   5. **Support.** The support of $y$ in population $k$ is $\{a\in\mathcal A^k: y^k_a>0\}$.
--   6. **Relative interior of $\mathrm{WE}(\Gamma)$.** The interior of $\mathrm{WE}(\Gamma)\subseteq\mathbb R^{\sqcup_k\mathcal A^k}$ relative to its affine hull.
--
--   **Formalization Note.** The printed Lagrangian writes $-\sum_k\lambda^k\big(\sum_a y^k_a\big)$ and omits $+\sum_k\lambda^k\gamma^k$; with that form no saddle point exists, since $\mathcal L(\hat y,\cdot)$ is unbounded above in $\lambda^k$. The definition here carries the $-\gamma^k$ of the equality constraint. The page writes the sign multipliers $\lambda_{a,k}$ in the Lagrangian and $\hat\lambda^k_a$ in the KKT conditions; they are the same object. The KKT conditions are exactly the printed list, which does not contain $\hat y\ge 0$. The relative interior is Mathlib's `intrinsicInterior`.
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, Lagrangian, KKT conditions and saddle-point display, p.19; relative interior and support, p.20

import Mathlib
import Definitions.Def_CorrWardrop_Model

open MeasureTheory

namespace CorrWardrop

variable {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
  [DecidableEq K] [∀ k, DecidableEq (A k)]

/-- The Lagrange multipliers `λ = ((λ^k)_{k ∈ K}, (λ^k_a)_{a ∈ A^k, k ∈ K})` of the problem
`min {Φ(y) : ∀ k, ∑_{a ∈ A^k} y^k_a = γ^k, ∀ k, ∀ a ∈ A^k, y^k_a ≥ 0}`: `λ.1 k = λ^k` for the
equality constraint of population `k`, and `λ.2 k a = λ^k_a` for the sign constraint on `y^k_a`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.19.

Formalization Note: the page writes these multipliers `λ_{a,k}` in the Lagrangian and `λ̂^k_a`
in the KKT conditions; both are `λ.2 k a` here. -/
abbrev Multipliers {K : Type*} (A : K → Type*) : Type _ := (K → ℝ) × Flow A

/-- The KKT conditions of `(ŷ, λ̂)` for `min {Φ(y) : y ∈ Y}`: for all `k ∈ K` and `a ∈ A^k`,
`∂Φ/∂y^k_a(ŷ) = λ̂^k + λ̂^k_a`, `λ̂^k_a · ŷ^k_a = 0`, `λ̂^k_a ≥ 0`, and
`∑_{a ∈ A^k} ŷ^k_a = γ^k`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, KKT conditions, p.19.

Formalization Note: the conditions are exactly the printed list; the sign constraint
`ŷ ≥ 0` (primal feasibility) is not part of it, as on the page. `∂Φ/∂y^k_a(ŷ)` is
`fderiv ℝ Φ ŷ (unitFlow k a)`. -/
def KKT (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (y : Flow A) (l : Multipliers A) : Prop :=
  (∀ k (a : A k),
    fderiv ℝ Φ y (unitFlow k a) = l.1 k + l.2 k a ∧ l.2 k a * y k a = 0 ∧ 0 ≤ l.2 k a) ∧
  ∀ k, ∑ a, y k a = Γ.γ k

/-- The Lagrangian of `min {Φ(y) : ∀ k, ∑_a y^k_a = γ^k, y ≥ 0}`:
`L(y, λ) = Φ(y) − ∑_k λ^k (∑_{a ∈ A^k} y^k_a − γ^k) − ∑_k ∑_{a ∈ A^k} λ^k_a y^k_a`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.19 (corrected).

Formalization Note: the printed Lagrangian omits the term `+ ∑_k λ^k γ^k` (it writes
`− ∑_k λ^k (∑_a y^k_a)`). With the printed form no pair `(ŷ, λ̂)` is a saddle point, because
`L(ŷ, ·)` is unbounded above in `λ^k`; the constraint `∑_a y^k_a = γ^k` requires the `− γ^k`.
-/
def lagrangian (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (y : Flow A) (l : Multipliers A) : ℝ :=
  Φ y - ∑ k, l.1 k * (∑ a, y k a - Γ.γ k) - ∑ k, ∑ a, l.2 k a * y k a

/-- `(ŷ, λ̂)` is a saddle point of the Lagrangian on `U × (ℝ^K × ℝ_{≥0}^{⊔A^k})`:
`ŷ ∈ U`, `λ̂^k_a ≥ 0` for all `k, a`, and for all `y ∈ U` and all `λ` with `λ^k_a ≥ 0`,
`L(ŷ, λ) ≤ L(ŷ, λ̂) ≤ L(y, λ̂)`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.19 (with Rockafellar
1970, Theorem 28.3).

Formalization Note: the page says "for all `(y, λ)`". The primal variable ranges over the domain
`U` of the potential (the open convex neighbourhood of `Y` on which `Φ` is convex), and the
multipliers of the sign constraints range over `λ^k_a ≥ 0` while the `λ^k` are free, as in
Rockafellar's Theorem 28.3. -/
def IsSaddle (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (U : Set (Flow A)) (y : Flow A)
    (l : Multipliers A) : Prop :=
  y ∈ U ∧ (∀ k (a : A k), 0 ≤ l.2 k a) ∧
    ∀ y' ∈ U, ∀ l' : Multipliers A, (∀ k (a : A k), 0 ≤ l'.2 k a) →
      lagrangian Γ Φ y l' ≤ lagrangian Γ Φ y l ∧ lagrangian Γ Φ y l ≤ lagrangian Γ Φ y' l

/-- The support of the flow profile `y` in population `k`: the actions `a ∈ A^k` with
`y^k_a > 0`.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.20 ("the support of all
flows"). -/
def support (y : Flow A) (k : K) : Set (A k) := {a | 0 < y k a}

/-- The relative interior of `WE(Γ)`, as a subset of the flow space.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.20.

Formalization Note: the relative interior is Mathlib's `intrinsicInterior` (the interior inside
the affine span) of the image of `WE(Γ) ⊆ Y` in the flow space. -/
def relintWE (Γ : NonatomicGame K A) : Set (Flow A) :=
  intrinsicInterior ℝ ((Subtype.val : Γ.Y → Flow A) '' WE Γ)

end CorrWardrop


