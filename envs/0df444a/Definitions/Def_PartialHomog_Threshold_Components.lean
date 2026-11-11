-- Prove2me | Definitions.Def_PartialHomog_Threshold_Components
-- name    : PartialHomog_Threshold_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:26:31.180312+00:00
-- url     : https://prove2.me/theorems/dd96bac3-4658-45c8-9b64-c743ca2fd467
-- title:
--   Homogeneous components $P^{[\ge d]}$, $P^{[\le d]}$; constant, affine, linear and quadratic forms; quadratic maps and their span $W$
-- statement:
--   Let $R$ be a commutative ring with $1$ and $z=(z_0,\dots,z_{N-1})$ variables. Polynomials are formal elements of $R[z]$. For $P\in R[z]$ and $i\ge 0$, $P^{[i]}$ is the homogeneous component of $P$ of degree $i$, and
--   $$P^{[\ge d]}=\sum_{i\ge d}P^{[i]},\qquad P^{[\le d]}=\sum_{i\le d}P^{[i]} .$$
--   A polynomial is **constant** if it equals some $c\in R$, **affine** if its total degree is at most $1$, a **linear form** if it is homogeneous of degree $1$, and a **quadratic form** if it is homogeneous of degree $2$ (the zero polynomial counts as both forms). A **quadratic map** $\phi=(\phi_0,\dots,\phi_{K-1})$ is a tuple of quadratic forms, and $W=\operatorname{span}_R\{\phi_0,\dots,\phi_{K-1}\}$ is the span of its coordinates.
--
--   **Formalization Note** `partGe d P` sums `homogeneousComponent i P` over `d ≤ i ≤ totalDegree P` (higher components vanish). `IsConstPoly P` is `∃ c, P = C c`; `IsAffine P` is `totalDegree P ≤ 1`; `IsLinearForm`/`IsQuadraticForm` are `IsHomogeneous 1`/`IsHomogeneous 2`.
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 12 (PDF 14), §A.1; p. 4 (PDF 6), §1.3; p. 26 (PDF 28), §E.2

import Mathlib

/-!
# Homogeneous components, constants, affine, linear and quadratic forms

Spiizer, *Partial Homogenization and the Structure of Optimal Algebraic Algorithms*,
STOC 2027 submission, §A.1 (p. 12) and §1.3 (p. 4).

Polynomials are formal: elements of `MvPolynomial (Fin N) R` in the variables `z = (z_0, …, z_{N-1})`
over a commutative ring `R` with `1`. `P^{[i]}` is Mathlib's `homogeneousComponent i P`.
-/

namespace PartialHomog.Threshold

open MvPolynomial

variable {R : Type*} [CommRing R] {N : ℕ}

/-- `P^{[≥d]} = ∑_{i ≥ d} P^{[i]}`: the part of `P` of degree at least `d` (§A.1). -/
noncomputable def partGe (d : ℕ) (P : MvPolynomial (Fin N) R) : MvPolynomial (Fin N) R :=
  ∑ i ∈ (Finset.range (P.totalDegree + 1)).filter (fun i => d ≤ i), homogeneousComponent i P

/-- `P^{[≤d]} = ∑_{i ≤ d} P^{[i]}`: the part of `P` of degree at most `d` (§A.1). -/
noncomputable def partLe (d : ℕ) (P : MvPolynomial (Fin N) R) : MvPolynomial (Fin N) R :=
  ∑ i ∈ Finset.range (d + 1), homogeneousComponent i P

/-- `P` is a constant polynomial: `P = c` for some `c ∈ R`. -/
def IsConstPoly (P : MvPolynomial (Fin N) R) : Prop :=
  ∃ c : R, P = C c

/-- `P` is affine: of total degree at most one (a constant plus a linear form). -/
def IsAffine (P : MvPolynomial (Fin N) R) : Prop :=
  P.totalDegree ≤ 1

/-- A linear form: a homogeneous polynomial of degree one (the zero polynomial included). -/
def IsLinearForm (P : MvPolynomial (Fin N) R) : Prop :=
  P.IsHomogeneous 1

/-- A quadratic form: a homogeneous polynomial of degree two (the zero polynomial included). -/
def IsQuadraticForm (P : MvPolynomial (Fin N) R) : Prop :=
  P.IsHomogeneous 2

/-- A quadratic map `ϕ = (ϕ_0, …, ϕ_{K-1})`: every coordinate is a quadratic form (§1.3). -/
def IsQuadraticMap {K : ℕ} (ϕ : Fin K → MvPolynomial (Fin N) R) : Prop :=
  ∀ s, IsQuadraticForm (ϕ s)

/-- The span `W = span_R {ϕ_0, …, ϕ_{K-1}}` of the coordinates of `ϕ`. -/
noncomputable def spanW {K : ℕ} (ϕ : Fin K → MvPolynomial (Fin N) R) : Submodule R (MvPolynomial (Fin N) R) :=
  Submodule.span R (Set.range ϕ)

end PartialHomog.Threshold


