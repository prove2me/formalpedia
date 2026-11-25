-- Prove2me | Definitions.Def_RPLib_FX_EtP1_13
-- name    : RPLib_FX_EtP1_13
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:39:27.3828+00:00
-- url     : https://prove2.me/theorems/64968e9f-e738-58e3-9cb4-b4bfc3f5714f
-- title:
--   Étale cohomology of the projective line, library file 13 of 34
-- statement:
--   File 13 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_35

/-!
# Étale cohomology of the projective line, library file 13 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Coh =====
section

/-!
# S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf

`H Λ F n := Ext^n(Λ_X, F)` in `EtSh Λ X` (a Grothendieck abelian category, so `Ext` exists and
there are enough injectives). Long exact sequences in `F` are Mathlib's
`Ext.covariant_sequence_exact₁/₂/₃` (E0Probe amendment A7).

Comparisons (via `extAdjEquiv`):
* `closedH`: for a closed immersion `i : Z ⟶ X`, `H^n(X, i_* G) ≃ H^n(Z, G)`;
* `openH`: for an open immersion `j : U ⟶ X`, `Ext^n_X(j_! Λ_U, F) ≃ H^n(U, F|_U)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtIso

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

end ExtIso

variable (Λ : Type u) [CommRing Λ]

/-- `H^n(X, -)` respects isomorphisms. -/
def Hiso {X : Scheme.{u}} {F G : EtSh Λ X} (e : F ≅ G) (n : ℕ) : H Λ F n ≃+ H Λ G n :=
  extIsoRight _ e n

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Cohomology of a closed pushforward**: `H^n(X, i_* G) ≃ H^n(Z, G)` for a closed immersion. -/
def closedH (G : EtSh Λ Z) (n : ℕ) : H Λ ((push i Λ).obj G) n ≃+ H Λ G n :=
  (extAdjEquiv (pullAdj i Λ) (unitSh Λ X) G n).symm.trans
    (extIsoLeft (pullConst Λ i (ModuleCat.of Λ Λ)).symm G n)

end Closed

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Cohomology of an open subscheme**: `Ext^n_X(j_! Λ_U, F) ≃ H^n(U, F|_U)`. -/
def openH (F : EtSh Λ X) (n : ℕ) :
    Ext ((lsh j Λ).obj (unitSh Λ U)) F n ≃+ H Λ ((res j Λ).obj F) n :=
  extAdjEquiv (lshAdj j Λ) (unitSh Λ U) F n

end Open

end RamanujanPetersson.EtCompact

end

end


