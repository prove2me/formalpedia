-- Prove2me | Definitions.Def_MatMulTimeLP_FixPoint
-- name    : MatMulTimeLP_FixPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:43.920681+00:00
-- url     : https://prove2.me/theorems/e67b172e-dfa8-4b62-ae3f-f4d9e4227536
-- title:
--   The fix point map, the regularizer $\psi$ and its Bregman divergence
-- statement:
--   For $H\in\mathbb R^{n\times n}$ and $h\in\mathbb R^n$, with $f(t)=\sqrt{t^2+4}-2$ applied coordinatewise, the **fix point equation** is $a=Hf(a)+h$. The residual at $z$ is $r=Hf(z)+h-z$, and $F(z)=z-Hf(z)-h=-r$.
--
--   A map $F$ is **$\beta$-co-coercive** if $\langle F(x)-F(y),x-y\rangle\ge\beta\|F(x)-F(y)\|_2^2$, and **$\mu$-strongly monotone with respect to $D$** if $\langle F(x)-F(y),x-y\rangle\ge\mu D(x,y)$. For a separable $\Psi(z)=\sum_i\psi_i(z_i)$ the Bregman divergence is
--
--   $$D_\Psi(x,z)=\sum_i\bigl(\psi_i(x_i)-\psi_i(z_i)-\psi_i'(z_i)(x_i-z_i)\bigr).$$
--
--   The regularizer of the algorithm is $\psi(t)=|t|/2-\log(1+|t|/2)$, with $\psi'(t)=t/(2(2+|t|))$ and $(\psi')^{-1}(y)=4y/(1-2|y|)$ on $(-1/2,1/2)$. The module also defines the reflection $H=Q-P$ with $Q=I-P$, the vector $h=-2Q(x\circ s/\tau'-\mathbf 1)$, and the recovery coordinates $\hat\xi_i=(\sqrt{\hat a_i^2+4}+\hat a_i)/2$, $\hat\sigma_i=(\sqrt{\hat a_i^2+4}-\hat a_i)/2$.
--
--   Together these state the recentering step of the interior point method as a fix point problem and fix the geometry in which that problem is solved.
--
--   **Formalization Note** $\psi'$ is the explicit formula of Lemma 5.5(ii), and the divergence uses it; the mission's verification file proves that it is the derivative of $\psi$ everywhere. Outside $(-1/2,1/2)$ the value of $(\psi')^{-1}$ has no meaning; every statement proves or assumes that its argument lies inside.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 2.2 p.7; Definitions 2.3, 2.7 pp.8–10; p.18; p.19; p.24; Lemma 5.5 pp.25–26

import Mathlib
import Definitions.Def_MatMulTimeLP_LP

namespace MatMulTimeLP

open Matrix

/-!
# The fix point equation, the regularizer and its Bregman divergence

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc): `f` Theorem 2.2 p.7; Definitions 2.3, 2.7 pp.8–10;
`H, h` p.18; the recovery formulas p.19; `ψ`, `Ψ` p.24; `ψ'`, `(ψ')⁻¹` Lemma 5.5 pp.25–26.

**Formalization Note** `dpsi` is the explicit formula for `ψ'` of Lemma 5.5(ii), and the Bregman
divergence uses it; the verification file proves `HasDerivAt psi (dpsi t) t`. `dpsiInv` is formula
(8), the inverse of `ψ'` on `(-1/2, 1/2)`; outside that interval its value has no meaning, and every
statement proves or assumes the argument lies inside.
-/

/-- `f(t) = √(t² + 4) - 2`, Theorem 2.2, p.7. -/
noncomputable def f (t : ℝ) : ℝ := Real.sqrt (t ^ 2 + 4) - 2

/-- `f` applied coordinatewise. -/
noncomputable def fv {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ := fun i => f (z i)

/-- The residual `r = Hf(z) + h - z`. -/
noncomputable def residual {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) : Fin n → ℝ :=
  H *ᵥ fv z + h - z

/-- The map `F(z) = z - Hf(z) - h = -r`, p.8. -/
noncomputable def fixF {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) : Fin n → ℝ :=
  z - H *ᵥ fv z - h

/-- `a` solves the fix point equation `a = Hf(a) + h`. -/
def IsFixPoint {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h a : Fin n → ℝ) : Prop :=
  a = H *ᵥ fv a + h

/-- `β`-co-coercivity, Definition 2.3, p.8. -/
def IsCoCoercive {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (β : ℝ) : Prop :=
  ∀ x y, β * ((F x - F y) ⬝ᵥ (F x - F y)) ≤ (F x - F y) ⬝ᵥ (x - y)

/-- The Bregman divergence of a separable function `Ψ(z) = ∑ᵢ ψᵢ(zᵢ)`, where `dψ i` is the derivative
of `ψ i`: `D_Ψ(x, z) = Ψ(x) - Ψ(z) - ⟨∇Ψ(z), x - z⟩`, p.10. -/
def bregmanSep {n : ℕ} (ψ dψ : Fin n → ℝ → ℝ) (x z : Fin n → ℝ) : ℝ :=
  ∑ i, (ψ i (x i) - ψ i (z i) - dψ i (z i) * (x i - z i))

/-- `μ`-strong monotonicity with respect to `D`, Definition 2.7, p.10. -/
def IsRelStronglyMonotone {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ)
    (D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (μ : ℝ) : Prop :=
  ∀ x y, μ * D x y ≤ (F x - F y) ⬝ᵥ (x - y)

/-- The regularizer `ψ(t) = |t|/2 - log(1 + |t|/2)`, p.24. -/
noncomputable def psi (t : ℝ) : ℝ := |t| / 2 - Real.log (1 + |t| / 2)

/-- `ψ'(t) = t / (2(2 + |t|))`, Lemma 5.5(ii), p.25. -/
noncomputable def dpsi (t : ℝ) : ℝ := t / (2 * (2 + |t|))

/-- `(ψ')⁻¹(y) = 4y / (1 - 2|y|)`, formula (8), p.26. -/
noncomputable def dpsiInv (y : ℝ) : ℝ := 4 * y / (1 - 2 * |y|)

/-- `D_Ψ(z, y)` for `Ψ(z) = ∑ᵢ ψ(zᵢ)`. -/
noncomputable def bregPsi {n : ℕ} (z y : Fin n → ℝ) : ℝ :=
  bregmanSep (fun _ => psi) (fun _ => dpsi) z y

/-- The reflection `H = Q - P`, with `Q = I - P`, p.18. -/
def ipmH {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - P) - P

/-- `h = -2Q(x ∘ s/τ' - 1)`, p.18. -/
noncomputable def ipmh {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (x s : Fin n → ℝ) (τ' : ℝ) :
    Fin n → ℝ :=
  (-2 : ℝ) • ((1 - P) *ᵥ fun i => x i * s i / τ' - 1)

/-- `ξ̂ᵢ = (√(âᵢ² + 4) + âᵢ)/2`, p.19. -/
noncomputable def xiHat {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (Real.sqrt (a i ^ 2 + 4) + a i) / 2

/-- `σ̂ᵢ = (√(âᵢ² + 4) - âᵢ)/2`, p.19. -/
noncomputable def sigmaHat {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (Real.sqrt (a i ^ 2 + 4) - a i) / 2

end MatMulTimeLP


