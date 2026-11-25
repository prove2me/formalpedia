-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_033
-- name    : RPLib_FX_EtPBC_033
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:59:45.701939+00:00
-- url     : https://prove2.me/theorems/694c3900-7a74-57ae-9129-623f2149fab9
-- title:
--   Proper base change for the projective line, library file 033
-- statement:
--   File 033 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_028
import Definitions.Def_RPLib_FX_EtPBC_029
import Definitions.Def_RPLib_FX_EtPBC_030

/-!
# Proper base change for the projective line, library file 033

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr
  RamanujanPetersson.EtCompact.GGerm RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

variable (Λ : Type u) [CommRing Λ]

/-! ### `Λ_U ⟶ g^* Λ_X` -/

/-- `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`. -/
def unitResIso : unitSh Λ U ≅ (res g Λ).obj (unitSh Λ X) :=
  @asIso _ _ _ _ (unitRes g Λ) (isIso_unitRes g Λ)

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E6b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object

* `resHE_comp_mk₀`, `freeEquiv_unitRes`, `unitRes_one`;
* `unitRes_comp`: `1 ↦ 1` along `m.left`, then along `W.hom`, is `1 ↦ 1` along `W'.hom`; `resCompIso_unit`;
* **`extFreeU_natural`**: `extFreeU W' (ξ ∘ Λ[m]) = resLE m.left (extFreeU W ξ)` in degree `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem resHE_comp_mk₀ {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {F G : EtSh Λ X} (f : F ⟶ G) {n : ℕ}
    (x : H Λ F n) :
    resHE g G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (resHE g F n x).comp (Ext.mk₀ ((res g Λ).map f)) (add_zero n) := by
  rw [resHE_apply, resHE_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

theorem resCompIso_unit {W W' : P.Etale} (m : W' ⟶ W) :
    (resCompIso Λ m).hom.app (unitSh Λ P) ≫ (unitResIso W'.hom Λ).inv =
      (res m.left Λ).map (unitResIso W.hom Λ).inv ≫ (unitResIso m.left Λ).inv := by
  have h : (unitResIso m.left Λ).hom ≫ (res m.left Λ).map (unitResIso W.hom Λ).hom ≫
      (resCompIso Λ m).hom.app (unitSh Λ P) = (unitResIso W'.hom Λ).hom := unitRes_comp m
  rw [Iso.comp_inv_eq, ← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]

end RamanujanPetersson.EtPBC.EtMV

end

end


