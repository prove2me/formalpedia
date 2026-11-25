-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_058
-- name    : RPLib_FX_EtPBC_058
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:27:53.517561+00:00
-- url     : https://prove2.me/theorems/dad5c7a6-0297-59f6-8498-68349b194e7f
-- title:
--   Proper base change for the projective line, library file 058
-- statement:
--   File 058 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_038
import Definitions.Def_RPLib_FX_EtPBC_044

/-!
# Proper base change for the projective line, library file 058

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
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

/-- **Restriction commutes with `extFree`.** -/
theorem extFreeV_restrict (W : P.Etale) (V : W.left.Etale) (F : EtSh Λ P) {n : ℕ}
    (β : Ext.{u} (freeSh Λ W) F n) :
    extFreeV Λ W V F n ((Ext.mk₀ (freeMap Λ (toW W V))).comp β (zero_add n)) =
      (Ext.mk₀ (freeMap Λ (toTop V) ≫ (unitIso Λ W.left).hom)).comp (extFree Λ W F n β) (zero_add n) := by
  rw [extFreeV_apply, extFree_apply, Ext.mk₀_comp_mk₀_assoc, ← extAdjMap_mk₀_comp, Ext.mk₀_comp_mk₀_assoc,
    lshFreeInv_toW]
  rfl

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality

Fix `D₀ R : P.Etale` with `W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`.
For `τ : T ⟶ D₀` (any `T : P.Etale` over `D₀`):
* **`theta Λ D₀ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`** (extension by zero to `D₀`, Shapiro for
  `W₀ ⟶ D₀`, pullback of free sheaves, `T ×_{D₀} W₀ ≅ T ×_P R`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm R m) (θ_{τ₂} x)` (`wm R m : T₁ ×_P R ⟶ T₂ ×_P R`);
* `extFreeV_natural` (naturality of `extFreeV` in `V`), `shapExt_symm_natural`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section ExtV

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **`extFreeV` is natural in `V`.** -/
theorem extFreeV_natural (W : P.Etale) {V₁ V : W.left.Etale} (v : V₁ ⟶ V) (F : EtSh Λ P) {k : ℕ}
    (x : Ext.{u} (freeSh Λ ((etComp W.hom).obj V)) F k) :
    extFreeV Λ W V₁ F k ((Ext.mk₀ (freeMap Λ ((etComp W.hom).map v))).comp x (zero_add k)) =
      (Ext.mk₀ (freeMap Λ v)).comp (extFreeV Λ W V F k x) (zero_add k) := by
  rw [extFreeV_apply, extFreeV_apply, Ext.mk₀_comp_mk₀_assoc, lshFreeInv_natural, ← Ext.mk₀_comp_mk₀_assoc]
  exact extAdjMap_mk₀_comp (lshAdj W.hom Λ) (freeMap Λ v) F _

end ExtV

section ShapNat

end ShapNat

section Theta

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end


