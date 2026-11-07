-- Prove2me | Definitions.Def_BorderD4_HasDEG
-- name    : BorderD4_HasDEG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:17.05889+00:00
-- url     : https://prove2.me/theorems/1e9b966b-25d7-4b4f-ac81-f9182d2b5fa8
-- title:
--   The degree $\mathrm{DEG}\,I$ of an ideal, through the affine Hilbert polynomial
-- statement:
--   For a proper ideal $I$ of $L[x]$, the affine Hilbert function is $\mathrm{HilbF}_I(s)=\dim_L L[x]_{\le s}/I_{\le s}$. It agrees for large $s$ with a polynomial $\mathrm{HilbP}_I$ of degree $d=\dim L[x]/I$, and
--   $$\mathrm{DEG}\,I=d!\cdot\mathrm{lc}(\mathrm{HilbP}_I).$$
--   The degree of an irreducible variety $V$ is $\mathrm{DEG}\,I(V)$.
--
--   **Formalization Note** `HasDEG I D` is a predicate: $I$ is proper and $D$ is this value for some polynomial agreeing eventually with the Hilbert function. Results conclude "there is $D$ with `HasDEG I D` and $D\le\dots$", so no junk value can satisfy a bound.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.2 "Degree and Hilbert Functions", p.31

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The affine Hilbert function `HilbF_I(s) = dim_L L[x]_{≤s} / I_{≤s}`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.2 "Degree and Hilbert Functions", p.31. -/
noncomputable def hilbF {L σ : Type*} [Field L] (I : Ideal (MvPolynomial σ L)) (s : ℕ) : ℕ :=
  Module.finrank L
    (restrictTotalDegree σ L s ⧸
      (I.restrictScalars L).comap (restrictTotalDegree σ L s).subtype)

/-- `DEG I = D`: the ideal `I` is proper, and `D = d! · lc(HilbP_I)`, where the Hilbert polynomial `HilbP_I`
agrees with the Hilbert function for all large `s` and has degree `d`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.2 "Degree and Hilbert Functions", p.31.

**Formalization Note** A predicate rather than a function, so no junk value can make a bound hold:
theorems conclude `∃ D, HasDEG I D ∧ D ≤ …`. The degree of an irreducible variety `V` is `DEG I(V)` (p.31),
so statements about `V` are stated for its prime ideal. The page's fact `d = dim L[x]/I` is a theorem there
and is not part of the definition; `d` is read off as the degree of the polynomial. -/
def HasDEG {L σ : Type*} [Field L] (I : Ideal (MvPolynomial σ L)) (D : ℕ) : Prop :=
  I ≠ ⊤ ∧ ∃ P : Polynomial ℚ,
    (∀ᶠ s in Filter.atTop, (hilbF I s : ℚ) = P.eval (s : ℚ)) ∧
      (D : ℚ) = (P.natDegree.factorial : ℚ) * P.leadingCoeff

end BorderD4


