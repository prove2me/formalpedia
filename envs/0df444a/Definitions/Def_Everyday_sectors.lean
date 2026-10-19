-- Prove2me | Definitions.Def_Everyday_sectors
-- name    : Everyday_sectors
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T00:11:43.700036+00:00
-- url     : https://prove2.me/theorems/939f99f4-1304-42ad-8a2e-76a55071262e
-- title:
--   The everyday sectors: gauge field, matter coupling, Higgs potential, and the assembled action
-- statement:
--   The source equation's action is assembled from labeled sectors: the other forces -(1/4) F_μν^a F^{aμν}, the matter coupling ψ̄_L V Φ ψ_R plus its hermitian conjugate, and the Higgs potential V(Φ). The bundle defines the sector vocabulary of the mission's arena. The gauge field of the discrete arena: an abelian field A on the oriented edges of the complete graph, A x y the connection along the edge (x, y), standing in for the components A_μ. The field strength: the curl of A around the triangle (x, y, z) — A x y - A x z + A y z — the discrete form of F = dA, standing in for F_μν. The gauge sector functional: the squared field strength summed against triangle weights w. The Yukawa term: the contraction of the left-handed fermion field with the coupling constant V and the Higgs field against the right-handed fermion field, summed over the spacetime. The Higgs potential in its Standard Model form: the Mexican hat -μ²|φ|² + λ|φ|⁴, the standard instantiation of the source's abstract V(Φ). And the assembled action: the four labeled sectors — gravity, the other forces (with the factor -(1/4) applied where the sector enters), matter (the Yukawa term plus its hermitian conjugate), and the Higgs potential sector — combined into one complex number, the action of a configuration.
--
--   **Formalization Note** The gauge sector is abelian: one real gauge field per oriented edge of the complete graph, with field strength the curl around triangles — the discrete exterior derivative of a 1-form, under which the gauge transformation is the shift of the edge field by a discrete gradient, exactly as in the continuum. The quartic coupling λ of the Mexican hat is bound as lam in the formal statement, λ being a reserved keyword in Lean 4. The fermion kinetic term i ψ̄ γ^μ D_μ ψ and the Higgs kinetic term -|D_μ Φ|² are not assembled — they require gamma-matrix and covariant-derivative structure beyond the arena; the definition's doc comment discloses this. The real-valued sectors enter the assembled action through their coercions to the complex numbers.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the gauge, matter, and Higgs sectors of the equation

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57

open ComplexConjugate
open scoped BigOperators

namespace Everyday

/-- The gauge field of the discrete arena: an abelian field A on the
oriented edges of the complete graph, A x y the connection along the
edge (x, y), standing in for the components A_μ. -/
def gaugeF {X : Type} (A : X → X → ℝ) : X → X → X → ℝ :=
  fun x y z => A x y - A x z + A y z

/-- The gauge sector functional: the squared field strength summed
against triangle weights w, standing in for -(1/4) ∫ d⁴x √(-g) F_μν^a
F^{aμν}; the factor -(1/4) is applied where the sector enters the
action. The field strength is the curl of the edge field around the
triangle (x, y, z) — the discrete form of F = dA. -/
def gaugeAction {X : Type} [Fintype X] (w : X → X → X → ℝ) (A : X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, w x y z * (gaugeF A x y z) ^ 2

/-- The Yukawa coupling on the discrete spacetime: the contraction of
the left-handed fermion field ψL with the coupling constant V and the
Higgs field Φh against the right-handed fermion field ψR, summed with
volume weights, standing in for ∫ d⁴x √(-g) ψ̄_L V Φ ψ_R. -/
def yukawaTerm {X : Type} [Fintype X] (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ) : ℂ :=
  ∑ x, conj (ψL x) * V * Φh x * ψR x

/-- The Higgs potential of the source equation in its Standard Model
form: the Mexican-hat potential -μ²|φ|² + λ|φ|⁴. The source writes the
potential as V(Φ) without unfolding it; the Standard Model potential it
denotes is this one. The quartic coupling λ is bound as lam, λ being a
reserved keyword in Lean 4. -/
def higgsV (μ lam : ℝ) (φ : ℂ) : ℝ :=
  -μ ^ 2 * Complex.normSq φ + lam * Complex.normSq φ ^ 2

/-- The Higgs potential sector: minus the potential energy of the
Higgs field on the discrete spacetime. -/
def higgsSum {X : Type} [Fintype X] (vol : X → ℝ) (μ lam : ℝ) (Φh : X → ℂ) : ℝ :=
  -∑ x, vol x * higgsV μ lam (Φh x)

/-- The action of the everyday equation: the four labeled sectors
assembled into one complex number — gravity (the Einstein–Hilbert sum),
the other forces (the gauge functional with its factor -(1/4)), matter
(the Yukawa term plus its hermitian conjugate), and the Higgs potential
sector. The real-valued sectors enter through their coercions to ℂ.
The fermion kinetic term i ψ̄ γ^μ D_μ ψ and the Higgs kinetic term
-|D_μ Φ|² are not assembled: they require gamma-matrix and
covariant-derivative structure beyond this arena; their contribution is
real by the same argument as the assembled terms. -/
noncomputable def everydayAction {X : Type} [Fintype X] (vol : X → ℝ) (w : X → X → X → ℝ)
    (mp : ℝ) (R : X → ℝ) (A : X → X → ℝ) (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ)
    (μ lam : ℝ) : ℂ :=
  ((gravSum vol mp R : ℝ) : ℂ)
    + ((-(1 / 4) * gaugeAction w A : ℝ) : ℂ)
    + (yukawaTerm ψL ψR V Φh + conj (yukawaTerm ψL ψR V Φh))
    + ((higgsSum vol μ lam Φh : ℝ) : ℂ)

end Everyday


