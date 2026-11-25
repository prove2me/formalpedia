-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_039
-- name    : RPLib_FX_EtPBC_039
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:01:16.349028+00:00
-- url     : https://prove2.me/theorems/65411be5-e66b-5db6-8b94-f757e97a800b
-- title:
--   Proper base change for the projective line, library file 039
-- statement:
--   File 039 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_033

/-!
# Proper base change for the projective line, library file 039

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2N1b =====
section

/-!
# S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map

* `hasExtEt`: a named (high priority) `HasExt` instance for etale sheaves;
* generic (any exact `Φ : C ⥤ D` of abelian categories): `mapExtU Φ u B n : Ext^n(A, B) →+ Ext^n(A', Φ B)`
  (`e ↦ mk₀ u ∘ Φ(e)`), `mapExtU_apply`, `mapSE` (image of a short exact sequence, end changed by `e : A' ≅ Φ A`),
  **`mapExtU_extClass`**;
* for an etale `g : U ⟶ X`: `resHE g F n := mapExtU (res g Λ) (unitRes g Λ) F n : H^n(X, F) →+ H^n(U, g^* F)`,
  `resHE_apply`, `resSE`, **`resHE_extClass`**.
The point transport and NAT (`trIso`, `galTrX`, `resHE_kappa`) are in O2N1c.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

section Gen

universe w v₁ u₁ v₂ u₂

end Gen

section Res

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Λ : Type u} [CommRing Λ]

/-- The restriction of `0 → G → P → Λ_X → 0`, ending in `Λ_U` through `unitResIso`. -/
theorem resSE {G P : EtSh Λ X} {f : G ⟶ P} {p : P ⟶ unitSh Λ X} {w : f ≫ p = 0}
    (hS : (ShortComplex.mk f p w).ShortExact) :
    (ShortComplex.mk ((res g Λ).map f) ((res g Λ).map p ≫ (unitResIso g Λ).inv)
      (by rw [← Category.assoc, ← Functor.map_comp, w, Functor.map_zero, zero_comp])).ShortExact :=
  mapSE (res g Λ) hS (unitResIso g Λ)

/-- **`resHE` of an extension class is the class of the restricted extension.** -/
theorem resHE_extClass {G P : EtSh Λ X} {f : G ⟶ P} {p : P ⟶ unitSh Λ X} {w : f ≫ p = 0}
    (hS : (ShortComplex.mk f p w).ShortExact) : resHE g G 1 hS.extClass = (resSE g hS).extClass :=
  mapExtU_extClass (res g Λ) hS (unitResIso g Λ)

end Res

end RamanujanPetersson.EtCompact.GalTrE

end

end


