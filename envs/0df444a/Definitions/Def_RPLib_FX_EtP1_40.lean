-- Prove2me | Definitions.Def_RPLib_FX_EtP1_40
-- name    : RPLib_FX_EtP1_40
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:13:33.220586+00:00
-- url     : https://prove2.me/theorems/dd1c54ee-b95a-5957-8a21-e2bedb2a08f0
-- title:
--   Étale cohomology of the projective line, library file 40 (an extra file from a re-cut)
-- statement:
--   File 40 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_24

/-!
# Étale cohomology of the projective line, library file 40 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Gm =====
section

/-!
# S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)

* `LX k = k[X]_X`: a domain, a principal ideal ring; `Algebra (LX k) k(X)` with `IsScalarTower` and
  `IsFractionRing`; **`LX.unit_eq`**: every unit of `k[X]_X` is `c X^m` in `k(X)`.
* `chartGm k : Spec k[X]_X ⟶ P^1_k` (open immersion), **`P1.opensRange_chartGm`**: its range is the overlap
  `range chartA1 ⊓ range chartA1'`.
* **`P1.h2EquivGm`**: `H^2(P^1, Λ) ≃ H^1(G_m, Λ)` when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section LX

variable (k : Type u) [Field k]

end LX

section Chart

variable (k : Type u) [Field k]

variable {Λ : Type u} [CommRing Λ]

/-- **`H^2(P^1, Λ) ≃ H^1(G_m, Λ)`** when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`. -/
def P1.h2EquivGm (h1 : Subsingleton (H Λ (unitSh Λ (A1 k)) 1)) (h2 : Subsingleton (H Λ (unitSh Λ (A1 k)) 2)) :
    H Λ (unitSh Λ (P1 k)) 2 ≃+ H Λ (unitSh Λ (Gm k)) 1 :=
  (P1.h2Equiv k h1 h2).trans (P1.h1InterEquiv k 1)

end Chart

end RamanujanPetersson.EtCompact

end

end


