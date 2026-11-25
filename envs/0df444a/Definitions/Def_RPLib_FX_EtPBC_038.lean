-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_038
-- name    : RPLib_FX_EtPBC_038
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:12:04.74318+00:00
-- url     : https://prove2.me/theorems/a82a4986-dbff-59b8-8a3d-b8a0a7e23200
-- title:
--   Proper base change for the projective line, library file 038
-- statement:
--   File 038 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_032
import Definitions.Def_RPLib_FX_EtPBC_033

/-!
# Proper base change for the projective line, library file 038

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

theorem extFreeV_apply (W : P.Etale) (V : W.left.Etale) (F : EtSh Λ P) (n : ℕ)
    (x : Ext.{u} (freeSh Λ ((etComp W.hom).obj V)) F n) :
    extFreeV Λ W V F n x = extAdjMap (lshAdj W.hom Λ) (freeSh Λ V) F n
      ((Ext.mk₀ (lshFreeInv Λ W.hom V)).comp x (zero_add n)) :=
  rfl

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

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

theorem unitResIso_hom : (unitResIso g Λ).hom = unitRes g Λ := rfl

end RamanujanPetersson.EtCompact.GalTrE

end

end


