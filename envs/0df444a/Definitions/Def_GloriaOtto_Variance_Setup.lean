-- Prove2me | Definitions.Def_GloriaOtto_Variance_Setup
-- name    : GloriaOtto_Variance_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:31.502326+00:00
-- url     : https://prove2.me/theorems/80f46e1f-cafb-4cc4-bcd9-1a02bf544424
-- title:
--   Lattice calculus on ℤ^d, conductivity functions A_αβ (Defs 2.1–2.4), the approximate corrector (2.3), the Green's function (2.11) and the averaging mask (3.15)
-- statement:
--   This file fixes the objects of Gloria and Otto's discrete stochastic homogenization setting.
--
--   1. **Lattice and edges.** Sites are points $x \in \mathbb Z^d$; $e_1,\dots,e_d$ is the canonical basis. An edge $[z, z+e_i]$ is encoded by the pair $(z, i)$, so every nearest-neighbour edge is listed exactly once. $|x|$ is the Euclidean norm of $x$, and $|v|^2 = \sum_i v_i^2$ for $v \in \mathbb R^d$.
--   2. **Conductivity functions (Definition 2.1).** A coefficient field assigns a conductivity $a(z,i) = a(z, z+e_i) = a(z+e_i, z)$ to each edge. It belongs to $\mathcal A_{\alpha\beta}$ if every value lies in $[\alpha, \beta]$; conductivities between non-neighbours are zero by construction.
--   3. **Discrete calculus (Definition 2.2).** $\nabla_i u(x) = u(x+e_i) - u(x)$, $\nabla^*_i u(x) = u(x) - u(x-e_i)$, $\nabla^*\cdot g(x) = \sum_i \big(g_i(x) - g_i(x-e_i)\big)$, and $A(x) = \mathrm{diag}[a(x,x+e_1),\dots,a(x,x+e_d)]$, so the elliptic operator is $Lu = -\nabla^*\cdot A\nabla u$.
--   4. **Approximate corrector (2.3).** For $T>0$ and $\xi \in \mathbb R^d$, $\phi_T(\cdot\,;a)$ is the unique bounded function $u : \mathbb Z^d \to \mathbb R$ with
--   $$T^{-1}u(x) - \nabla^*\cdot A(x)\big(\nabla u(x) + \xi\big) = 0 \qquad \text{for all } x \in \mathbb Z^d .$$
--   5. **Green's function (Definition 2.7, (2.11)).** For $T > 0$ and $y \in \mathbb Z^d$, $G_T(\cdot, y; a)$ is the unique $g \in \ell^2(\mathbb Z^d)$ with
--   $$\sum_{x} T^{-1} g(x) v(x) + \sum_x \nabla v(x)\cdot A(x)\nabla g(x) = v(y) \qquad \text{for all } v \in \ell^2(\mathbb Z^d).$$
--   6. **Law (Definition 2.4).** For a probability measure $\nu$ on $\mathbb R$, the i.i.d. law of the conductivities is the product measure $\nu^{\otimes E}$ over all edges.
--   7. **Mask (3.15).** $\eta_L : \mathbb Z^d \to [0,1]$ is supported in the open box $(-L,L)^d$, has $\sum_x \eta_L(x) = 1$, and satisfies $|\eta_L(x+e_i) - \eta_L(x)| \le C_\eta L^{-d-1}$ for all $x, i$.
--   8. **Averaged energy density.** The quantity of Theorem 2.1 is
--   $$\xi\cdot A_{L,T}\xi = \sum_{x\in\mathbb Z^d}\Big(T^{-1}\phi_T(x)^2 + \big(\nabla\phi_T(x)+\xi\big)\cdot A(x)\big(\nabla\phi_T(x)+\xi\big)\Big)\eta_L(x).$$
--   9. **Ball average.** $\bar f_{\{|x-y|\le R\}}$ is the mean of $f$ over the finite set $\{x \in \mathbb Z^d : |x-y| \le R\}$.
--
--   Every statement of the mission is phrased in terms of these objects.
--
--   **Formalization Note.** A coefficient field is a function on `Site d × Fin d`; the pair `(z, i)` stands for the edge $[z,z+e_i]$, which is literally the diagonal of $A(z)$ in (2.1) and makes Definition 2.1's symmetry and nearest-neighbour conditions hold by construction. The paper's $\phi_T$ is the unique *stationary* mean-zero solution of (2.3) (Lemma 2.2). For fixed $a \in \mathcal A_{\alpha\beta}$ and $T>0$, $T^{-1}+L$ is invertible on bounded functions (maximum principle), so (2.3) has exactly one bounded solution. This solution commutes with lattice shifts of $a$, is a measurable function of $a$ and is bounded. It is therefore stationary under the i.i.d. law and square-integrable, and taking expectations in (2.3) gives $\langle\phi_T\rangle = 0$. By the uniqueness in Lemma 2.2 it is the paper's $\phi_T$. `phiT` and `greenT` return $0$ where the defining problem has no unique solution; that does not happen for $a \in \mathcal A_{\alpha\beta}$ and $T>0$ (milestones *Lemma 2.2 (pathwise)* and *Definition 2.7*). Definition 2.7 prints the codomain of $G_T$ as $\mathbb Z^d$; it is real-valued (Lemma 2.5 writes $\to\mathbb R$). The componentwise gradient bound on $\eta_L$ is equivalent to the paper's bound on $|\nabla\eta_L|$ up to the factor $\sqrt d$, which the constant $C_\eta$ absorbs.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Definitions 2.1–2.4 and 2.7, (2.1), (2.3), (2.11), Theorem 2.1, (3.15), pp. 9–11, 16, 28

import Mathlib

open MeasureTheory

namespace GloriaOtto.Variance

/-- A lattice site `x ∈ ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The canonical basis vector `e_i` of `ℤ^d`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- An edge `[z, z + e_i]` of `ℤ^d`, encoded by the pair `(z, i)`; each unordered
nearest-neighbour edge is listed exactly once. -/
abbrev Edge (d : ℕ) := Site d × Fin d

/-- Membership in `A_{αβ}` (Definition 2.1): every edge conductivity lies in `[α, β]`.
The coefficient field `a : Edge d → ℝ` stores `a (z, i) = a(z, z + e_i) = a(z + e_i, z)`. -/
def InA {d : ℕ} (α β : ℝ) (a : Edge d → ℝ) : Prop :=
  ∀ e, a e ∈ Set.Icc α β

/-- Euclidean norm `|x|` of a lattice point. -/
noncomputable def latNorm {d : ℕ} (x : Site d) : ℝ :=
  Real.sqrt (∑ i, ((x i : ℤ) : ℝ) ^ 2)

/-- Squared Euclidean norm `|v|²` of a vector of `ℝ^d`. -/
def sqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- Forward discrete gradient: `∇_i u(x) = u(x + e_i) - u(x)` (Definition 2.2). -/
def grad {d : ℕ} (u : Site d → ℝ) (x : Site d) (i : Fin d) : ℝ :=
  u (x + unit i) - u x

/-- Backward discrete gradient: `∇*_i u(x) = u(x) - u(x - e_i)` (Definition 2.2). -/
def gradStar {d : ℕ} (u : Site d → ℝ) (x : Site d) (i : Fin d) : ℝ :=
  u x - u (x - unit i)

/-- Backward discrete divergence of a vector field:
`∇*·g(x) = ∑_i (g_i(x) - g_i(x - e_i))`. -/
def divStar {d : ℕ} (g : Site d → Fin d → ℝ) (x : Site d) : ℝ :=
  ∑ i, (g x i - g (x - unit i) i)

/-- The flux `A(x)(∇u(x) + ξ)`, with `A(x) = diag[a(x, x+e_1), …, a(x, x+e_d)]`. -/
def flux {d : ℕ} (a : Edge d → ℝ) (u : Site d → ℝ) (ξ : Fin d → ℝ)
    (x : Site d) (i : Fin d) : ℝ :=
  a (x, i) * (grad u x i + ξ i)

/-- `u` is a bounded solution of the approximate corrector equation (2.3):
`T⁻¹ u(x) - ∇*·A(x)(∇u(x) + ξ) = 0` for all `x ∈ ℤ^d`. -/
def IsApproxCorrector {d : ℕ} (a : Edge d → ℝ) (T : ℝ) (ξ : Fin d → ℝ)
    (u : Site d → ℝ) : Prop :=
  (∃ M : ℝ, ∀ x, |u x| ≤ M) ∧ ∀ x, T⁻¹ * u x - divStar (flux a u ξ) x = 0

open scoped Classical in
/-- The approximate corrector `φ_T(·; a)` in direction `ξ`: the unique bounded solution of
(2.3) when it exists and is unique (the case `a ∈ A_{αβ}`, `T > 0`), and `0` otherwise. -/
noncomputable def phiT {d : ℕ} (a : Edge d → ℝ) (T : ℝ) (ξ : Fin d → ℝ) : Site d → ℝ :=
  if h : ∃! u, IsApproxCorrector a T ξ u then h.exists.choose else 0

/-- `g = G_T(·, y; a)` solves the weak Green's-function equation (2.11) in `ℓ²(ℤ^d)`:
`∑_x T⁻¹ g(x) v(x) + ∑_x ∇v(x)·A(x)∇g(x) = v(y)` for every `v ∈ ℓ²(ℤ^d)`. -/
def IsGreen {d : ℕ} (a : Edge d → ℝ) (T : ℝ) (y : Site d) (g : Site d → ℝ) : Prop :=
  Summable (fun x => g x ^ 2) ∧
    ∀ v : Site d → ℝ, Summable (fun x => v x ^ 2) →
      ∑' x, T⁻¹ * g x * v x + ∑' x, ∑ i, grad v x i * a (x, i) * grad g x i = v y

open scoped Classical in
/-- The Green's function `G_T(x, y; a)` of Definition 2.7: the value at `x` of the unique
`ℓ²` solution of (2.11) with pole `y` (and `0` if there is no unique solution). -/
noncomputable def greenT {d : ℕ} (a : Edge d → ℝ) (T : ℝ) (x y : Site d) : ℝ :=
  if h : ∃! g, IsGreen a T y g then h.exists.choose x else 0

/-- The i.i.d. law of the conductivities (Definition 2.4): the product over all edges of a
single law `ν` on `ℝ`. -/
noncomputable def law (d : ℕ) (ν : Measure ℝ) : Measure (Edge d → ℝ) :=
  Measure.infinitePi (fun _ : Edge d => ν)

/-- The averaging mask of (3.15), with the implicit constant of `|∇η_L| ≲ L^{-d-1}` made
explicit as `Cη`: `0 ≤ η ≤ 1`, `supp η ⊂ (-L, L)^d`, `∑_x η(x) = 1`, and every
forward difference of `η` is at most `Cη L^{-d-1}` in absolute value. -/
def IsMask {d : ℕ} (L Cη : ℝ) (η : Site d → ℝ) : Prop :=
  (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
    (∀ x, η x ≠ 0 → ∀ i, |((x i : ℤ) : ℝ)| < L) ∧
    ∑' x, η x = 1 ∧
    ∀ x i, |η (x + unit i) - η x| ≤ Cη * L ^ (-(d : ℝ) - 1)

/-- The averaged energy density
`ξ·A_{L,T}ξ = ∑_x (T⁻¹ φ_T(x)² + (∇φ_T(x) + ξ)·A(x)(∇φ_T(x) + ξ)) η(x)`. -/
noncomputable def energyAvg {d : ℕ} (a : Edge d → ℝ) (T : ℝ) (ξ : Fin d → ℝ)
    (η : Site d → ℝ) : ℝ :=
  ∑' x, (T⁻¹ * phiT a T ξ x ^ 2 + ∑ i, a (x, i) * (grad (phiT a T ξ) x i + ξ i) ^ 2) * η x

/-- The average of `f` over the lattice ball `{x ∈ ℤ^d : |x - y| ≤ R}`. -/
noncomputable def ballAvg {d : ℕ} (f : Site d → ℝ) (y : Site d) (R : ℝ) : ℝ :=
  (∑' x, {x : Site d | latNorm (x - y) ≤ R}.indicator f x) /
    (Nat.card {x : Site d // latNorm (x - y) ≤ R} : ℝ)

end GloriaOtto.Variance


