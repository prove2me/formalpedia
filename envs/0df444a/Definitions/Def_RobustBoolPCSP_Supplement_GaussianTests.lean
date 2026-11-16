-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_GaussianTests
-- name    : RobustBoolPCSP_Supplement_GaussianTests
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:50.720999+00:00
-- url     : https://prove2.me/theorems/134e25af-7ac4-4afb-9efa-3330e861ccc8
-- title:
--   The three Gaussian tests of §10.2
-- statement:
--   Let $H$ be the five-cycle on $B=\mathbb Z/5\mathbb Z$ joining colors that differ by $\pm2$, and let $F:\mathbb R^d\to\Delta(B)$, $G:\mathbb R^{2d}\to\Delta(B)$ be measurable fuzzy colorings. With $Z,W,H_0$ independent standard Gaussian vectors in $\mathbb R^d$,
--
--   $$U=\sqrt{1-v}\,Z+\sqrt v\,W,\qquad V=-\sqrt{1-v}\,Z+\sqrt v\,W,$$
--
--   the **antipodal cost** $A$ is the probability that colors drawn from $F(Z)$, $F(-Z)$ do not form an $H$-edge; the **erasure cost** $E$ the probability that colors from $F(U)$, $F(V)$, $G(-W,H_0)$ contain no $H$-edge; the **equality cost** $N$ the probability that two independently drawn $G$-colors with inputs of correlation $1-v^2$ in all $2d$ coordinates disagree.
--
--   These costs are the Gaussian core of the obstruction for $\Lambda^{=}$ (Theorem 10.4).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §10.2, p.83, eq. (93)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RobustBoolPCSP.Supplement

/-- The edges of the five-cycle `H` on `B = Z/5Z` (p.83): "Let H be the five-cycle on B = Z/5Z whose
edges join colors differing by ±2." -/
def hEdge (b b' : ZMod 5) : Bool := decide (b - b' = 2) || decide (b - b' = -2)

/-- Three colors contain no edge of `H`. -/
def noEdge3 (b₁ b₂ b₃ : ZMod 5) : Bool := !(hEdge b₁ b₂ || hEdge b₁ b₃ || hEdge b₂ b₃)

/-- `F : X → ∆(B)` is a measurable **fuzzy coloring** (p.83): "arbitrary measurable simplex-valued
functions, where ∆(B) denotes the simplex of probability distributions on B." -/
def IsFuzzy {X : Type} [MeasurableSpace X] (F : X → ZMod 5 → ℝ) : Prop :=
  Measurable F ∧ ∀ x, (∀ b, 0 ≤ F x b) ∧ ∑ b, F x b = 1

/-- The standard Gaussian measure on `ℝ^d` (independent `N(0,1)` coordinates). -/
noncomputable def stdGauss (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- The **antipodal cost `A`** (§10.2, p.83): "The antipodal cost A tests the two colors from
F(Z), F(−Z) for an H-edge", `Z` a standard Gaussian vector in `ℝ^d`; the two requested colors are
drawn independently given their inputs; `A` is the rejection probability. -/
noncomputable def costA {d : ℕ} (F : (Fin d → ℝ) → ZMod 5 → ℝ) : ℝ :=
  ∫ z, ∑ b, ∑ b', F z b * F (-z) b' * (if hEdge b b' then 0 else 1) ∂(stdGauss d)

/-- The **erasure cost `E`** (§10.2, p.83): with `Z, W, H₀` independent standard Gaussian vectors in
`ℝ^d`, `U = √(1−v) Z + √v W`, `V = −√(1−v) Z + √v W` (93), "the erasure cost E tests whether colors
from F(U), F(V), G(−W, H₀) contain an H-edge"; `E` is the rejection probability, the three colors
drawn independently given their inputs. `G` reads `(−W, H₀) ∈ ℝ^{2d}` (as `ℝ^{d+d}`). -/
noncomputable def costE {d : ℕ} (v : ℝ) (F : (Fin d → ℝ) → ZMod 5 → ℝ)
    (G : (Fin (d + d) → ℝ) → ZMod 5 → ℝ) : ℝ :=
  ∫ p, (let Z := p.1; let W := p.2.1; let H0 := p.2.2
        let U := Real.sqrt (1 - v) • Z + Real.sqrt v • W
        let V := (-Real.sqrt (1 - v)) • Z + Real.sqrt v • W
        ∑ b₁, ∑ b₂, ∑ b₃, F U b₁ * F V b₂ * G (Fin.append (-W) H0) b₃ *
          (if noEdge3 b₁ b₂ b₃ then 1 else 0))
    ∂((stdGauss d).prod ((stdGauss d).prod (stdGauss d)))

/-- The **equality cost `N`** (§10.2, p.83): "the disagreement of two independently drawn G-colors
whose Gaussian inputs have correlation 1 − v² in all 2d coordinates": with `X, Y` independent
standard Gaussian vectors in `ℝ^{2d}` and `ρ = 1 − v²`, the inputs are `X` and
`ρ X + √(1 − ρ²) Y`. -/
noncomputable def costN {d : ℕ} (v : ℝ) (G : (Fin (d + d) → ℝ) → ZMod 5 → ℝ) : ℝ :=
  ∫ p, (let ρ := 1 - v ^ 2
        ∑ b, ∑ b', G p.1 b * G (ρ • p.1 + Real.sqrt (1 - ρ ^ 2) • p.2) b' *
          (if b = b' then 0 else 1))
    ∂((stdGauss (d + d)).prod (stdGauss (d + d)))

end RobustBoolPCSP.Supplement


