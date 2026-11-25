-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_044
-- name    : RPLib_FX_EtPBC_044
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:36:07.410088+00:00
-- url     : https://prove2.me/theorems/bb817df1-ed67-5c5d-a08e-7b8cf12c44e9
-- title:
--   Proper base change for the projective line, library file 044
-- statement:
--   File 044 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_037

/-!
# Proper base change for the projective line, library file 044

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

end GenFl

section Obj

variable {P : Scheme.{u}}

theorem extFree_apply (W : P.Etale) (F : EtSh Λ P) (n : ℕ) (β : Ext.{u} (freeSh Λ W) F n) :
    extFree Λ W F n β = extAdjMap (lshAdj W.hom Λ) (unitSh Λ W.left) F n
      ((Ext.mk₀ (freeLshIso Λ W).inv).comp β (zero_add n)) :=
  extAdjIsoGen_apply (lshAdj W.hom Λ) (freeLshIso Λ W) F n β

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end


