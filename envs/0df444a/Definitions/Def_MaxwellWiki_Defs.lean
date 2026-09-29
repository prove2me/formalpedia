-- Prove2me | Definitions.Def_MaxwellWiki_Defs
-- name    : MaxwellWiki_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T19:12:43.17127+00:00
-- url     : https://prove2.me/theorems/ea188fee-3aa6-4c40-9931-177043f60fed
-- title:
--   Vector calculus on $\mathbb{R}^3$ and Maxwell's microscopic equations (SI)
-- statement:
--   Vector calculus on $\mathbb{R}^3$ and Maxwell's microscopic equations in SI units.
--
--   1. **Vectors.** $\mathbb{R}^3$ is represented by coordinate triples $x=(x_0,x_1,x_2)$.
--   2. **Partial derivatives.** For a scalar field $f:\mathbb{R}^3\to\mathbb{R}$, $\partial_i f(x)$ is the Fréchet derivative of $f$ at $x$ applied to the $i$-th standard basis vector $e_i$.
--   3. **Divergence and curl.** For a vector field $F=(F_0,F_1,F_2)$,
--   $$\nabla\cdot F=\partial_0F_0+\partial_1F_1+\partial_2F_2,\qquad \nabla\times F=\big(\partial_1F_2-\partial_2F_1,\ \partial_2F_0-\partial_0F_2,\ \partial_0F_1-\partial_1F_0\big).$$
--   4. **Time derivative.** For a time-dependent field $F(t,x)$, $\partial_t F(t,x)$ is the derivative of $s\mapsto F(s,x)$ at $s=t$.
--   5. **Maxwell's equations.** Given constants $\varepsilon_0,\mu_0$, fields $\mathbf E,\mathbf B,\mathbf J:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ and a charge density $\rho:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$, the predicate *Maxwell solution* asserts that at every time $t$ and every point $x$
--   $$\nabla\cdot\mathbf E=\frac{\rho}{\varepsilon_0},\qquad \nabla\cdot\mathbf B=0,\qquad \nabla\times\mathbf E=-\frac{\partial\mathbf B}{\partial t},\qquad \nabla\times\mathbf B=\mu_0\Big(\mathbf J+\varepsilon_0\frac{\partial\mathbf E}{\partial t}\Big).$$
--   6. **Flux through a box.** For $a\le b$ in $\mathbb{R}^3$ and the box $\Omega=[a_0,b_0]\times[a_1,b_1]\times[a_2,b_2]$, the outward flux of $F$ through $\partial\Omega$ is
--   $$\oint_{\partial\Omega}F\cdot d\mathbf S=\sum_{i=0}^{2}\Big(\int_{\text{face }x_i=b_i}F_i\,dA-\int_{\text{face }x_i=a_i}F_i\,dA\Big),$$
--   each face integral being a two-dimensional Lebesgue integral over the remaining two coordinates.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Derivatives are Mathlib's `fderiv`/`deriv`, which return $0$ at points of non-differentiability; all theorems of the mission therefore assume explicit smoothness. The flux is only defined for rectangular boxes, which is the setting in which Mathlib's divergence theorem is available.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Summary — Microscopic version in SI units" (p. 2 of the snapshot), "Key to the notation" (pp. 4–5), and "Integral equations" (p. 5).

import Mathlib

namespace MaxwellWiki

/-- Vectors in three-dimensional space, as coordinate triples. -/
abbrev Vec3 := Fin 3 → ℝ

/-- The partial derivative `∂f/∂xᵢ` of a scalar field at `x`. -/
noncomputable def partialDeriv (i : Fin 3) (f : Vec3 → ℝ) (x : Vec3) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The divergence `∇ · F` of a vector field. -/
noncomputable def div (F : Vec3 → Vec3) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, partialDeriv i (fun y => F y i) x

/-- The curl `∇ × F` of a vector field. -/
noncomputable def curl (F : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  ![partialDeriv 1 (fun y => F y 2) x - partialDeriv 2 (fun y => F y 1) x,
    partialDeriv 2 (fun y => F y 0) x - partialDeriv 0 (fun y => F y 2) x,
    partialDeriv 0 (fun y => F y 1) x - partialDeriv 1 (fun y => F y 0) x]

/-- The partial time derivative `∂F/∂t` of a time-dependent field at `(t, x)`. -/
noncomputable def timeDeriv {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (F : ℝ → Vec3 → β) (t : ℝ) (x : Vec3) : β :=
  deriv (fun s => F s x) t

/-- Maxwell's microscopic equations in SI units (Gauss's law, Gauss's law for magnetism,
Faraday's law, Ampère–Maxwell law), holding at every time and every point of space. -/
structure IsMaxwellSolution (ε₀ μ₀ : ℝ) (E B J : ℝ → Vec3 → Vec3) (ρ : ℝ → Vec3 → ℝ) :
    Prop where
  gauss : ∀ t x, div (E t) x = ρ t x / ε₀
  gauss_magnetism : ∀ t x, div (B t) x = 0
  faraday : ∀ t x, curl (E t) x = -timeDeriv B t x
  ampere_maxwell : ∀ t x, curl (B t) x = μ₀ • (J t x + ε₀ • timeDeriv E t x)

/-- The outward flux `∯_{∂Ω} F · dS` of a vector field through the boundary of the
rectangular box `Ω = [a₀,b₀] × [a₁,b₁] × [a₂,b₂]`: for each coordinate direction `i`, the
integral of `Fᵢ` over the face `xᵢ = bᵢ` minus its integral over the face `xᵢ = aᵢ`. -/
noncomputable def boxFlux (F : Vec3 → Vec3) (a b : Vec3) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

end MaxwellWiki


