-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_025
-- name    : RPLib_FX_EtPBC_025
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:15:45.87372+00:00
-- url     : https://prove2.me/theorems/db0660ea-ca45-5adb-ae19-688fc25b8131
-- title:
--   Proper base change for the projective line, library file 025
-- statement:
--   File 025 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
--   * `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_021

/-!
# Proper base change for the projective line, library file 025

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1b`: S4-EtPBC-A, O2 M5 N1b: restriction of `H^n` along an etale map
* `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
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

theorem unitRes_coord (x : U) (c : Λ) :
    (constStalkIso Λ (geomPtAt (g x)) (ModuleCat.of Λ Λ)).hom.hom ((resTrIsoE g x Λ (unitSh Λ X)).hom.hom
      ((((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom (c • oneStalk Λ x))) = c := by
  rw [map_smul, map_smul, resTrIsoE_unitRes, map_smul, oneStalk_hom, smul_eq_mul, mul_one]

end RamanujanPetersson.EtCompact.GalTrE

end

end

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

/-- **Restriction on cohomology along an etale map** `H^n(X, F) → H^n(U, g^* F)`. -/
def resHE (F : EtSh Λ X) (n : ℕ) : H Λ F n →+ H Λ ((res g Λ).obj F) n :=
  mapExtU (res g Λ) (unitRes g Λ) F n

end Res

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L2x =====
section

/-!
# S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps

* `mapExact_iso τ ξ`: isomorphic exact functors act alike on `Ext¹` (`τ : Φ ≅ Φ'`);
* `conjE x a b := mk₀ a ∘ x ∘ mk₀ b`, `conjE_conjE`, `mapExact_conjE`;
* `pullUnit_comp`: `Λ_X ≅ (f ≫ g)^*Λ_Z ≅ f^*g^*Λ_Z` is `Λ_X ≅ f^*Λ_Y ≅ f^*g^*Λ_Z`;
* **`pullH_comp`**: `pullH (f ≫ g) 1 κ = pullH f 1 (pullH g 1 κ)`;
* `pullUnit_res`: for etale `g`, `Λ_U ≅ g^*Λ_X ≅ res g Λ_X` is `unitRes g`;
* **`resLE_eq_pullH`**: for etale `g`, `resLE g 1 e = pullH g 1 e`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE

section IsoGen

universe w v₁ u₁ v₂ u₂

end IsoGen

universe u

section PullX

variable {Λ : Type u} [CommRing Λ]

theorem pullH_eq_conjE {X Y : Scheme.{u}} (g : X ⟶ Y) (κ : H Λ (unitSh Λ Y) 1) :
    pullH Λ g 1 κ = conjE (κ.mapExactFunctor (pull g Λ)) (pullUnit Λ g).hom (pullUnit Λ g).inv := rfl

/-- **`pullH` along a composite** (degree one). -/
theorem pullH_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (κ : H Λ (unitSh Λ Z) 1) :
    pullH Λ (f ≫ g) 1 κ = pullH Λ f 1 (pullH Λ g 1 κ) := by
  rw [pullH_eq_conjE, pullH_eq_conjE, pullH_eq_conjE, mapExact_conjE, conjE_conjE,
    conjE_of_iso (pullCompIso Λ f g).symm κ, mapExact_compF (pull g Λ) (pull f Λ) κ, conjE_conjE]
  simp only [Iso.symm_inv, Iso.symm_hom]
  rw [pullUnit_comp, pullUnit_comp_inv]

end PullX

end RamanujanPetersson.EtPBC.EtMV

end

end


