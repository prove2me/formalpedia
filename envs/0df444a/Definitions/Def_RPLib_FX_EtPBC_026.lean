-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_026
-- name    : RPLib_FX_EtPBC_026
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:26:09.929634+00:00
-- url     : https://prove2.me/theorems/16a69f91-acf6-5125-9c4b-7b341f73a137
-- title:
--   Proper base change for the projective line, library file 026
-- statement:
--   File 026 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_021

/-!
# Proper base change for the projective line, library file 026

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Coh =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces

* **`unitRes_eq_adj W`**: `Λ_W ⟶ W^* Λ_X` (`1 ↦ 1`) is the adjunction unit followed by
  `W^*(Λ[W] ⟶ Λ[X] ≅ Λ_X)`;
* **`resLE_eq_extFreeU W c`**: `resLE W.hom 1 c = extFreeU W 1 (Λ[W ⟶ X]^* c)`;
* `extFreeU_splitIn`, **`h1_eq_zero_of_pieces`** (a class vanishing on every piece of a clopen decomposition is `0`),
  `splitIn_splitPr`, `resLE_splitPr(_self/_ne)`, **`resLE_kapS_self`**, **`resLE_kapS_ne`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtCompact.GalTrE

universe u

section Coh

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- **`1 ↦ 1` through the adjunction.** -/
theorem unitRes_eq_adj (W : X.Etale) :
    unitRes W.hom Λ = (lshAdj W.hom Λ).unit.app (unitSh Λ W.left) ≫
      (res W.hom Λ).map ((freeLshIso Λ W).inv ≫ freeMap Λ (toTop W) ≫ (unitIso Λ X).hom) := by
  rw [← cancel_epi (unitIso Λ W.left).hom]
  apply (freeEquiv Λ (etId W.left) _).injective
  rw [freeEquiv_unitRes]
  have hn : (unitIso Λ W.left).hom ≫ (lshAdj W.hom Λ).unit.app (unitSh Λ W.left) =
      (lshAdj W.hom Λ).unit.app (freeSh Λ (etId W.left)) ≫
        (res W.hom Λ).map ((lsh W.hom Λ).map (unitIso Λ W.left).hom) :=
    (lshAdj W.hom Λ).unit.naturality (unitIso Λ W.left).hom
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp, lsh_unit_freeLshIso,
    CategoryTheory.Functor.map_comp, ← Category.assoc, lshFreeInv_adj, freeEquiv_comp, AddEquiv.apply_symm_apply]
  have hfin : freeEquiv Λ ((etComp W.hom).obj (etId W.left)) (unitSh Λ X)
      (freeMap Λ (toTop ((etComp W.hom).obj (etId W.left))) ≫ (unitIso Λ X).hom) = oneRes W.hom Λ := by
    rw [freeEquiv_freeMap, unitIso_hom, freeToUnit]
    exact congrArg (fun s => ((unitSh Λ X).obj.map (toTop ((etComp W.hom).obj (etId W.left))).op).hom s)
      (AddEquiv.apply_symm_apply (freeEquiv Λ (etId X) (unitSh Λ X)) (oneSec Λ X))
  have hc := freeEquiv_comp Λ ((etComp W.hom).obj (etId W.left)) (𝟙 _)
    (freeMap Λ (toTop ((etComp W.hom).obj (etId W.left))) ≫ (unitIso Λ X).hom)
  rw [Category.id_comp] at hc
  exact hfin.symm.trans hc

end Coh

section Pieces

end Pieces

end RamanujanPetersson.EtPBC.EtKum

end

end


