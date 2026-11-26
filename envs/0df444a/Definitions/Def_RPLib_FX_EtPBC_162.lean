-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_162
-- name    : RPLib_FX_EtPBC_162
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:46:10.357384+00:00
-- url     : https://prove2.me/theorems/b700e835-a317-520a-889e-bf40cf989f0b
-- title:
--   Proper base change for the projective line, library file 162
-- statement:
--   File 162 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2T4b`: S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
--   * `S4.Def_RP_EtPBC_A_StkBCb`: S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
--   * `S4.Def_RP_EtPBC_A_StkBCc0`: S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_055
import Definitions.Def_RPLib_FX_EtPBC_154

/-!
# Proper base change for the projective line, library file 162

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2T4b`: S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
* `S4.Def_RP_EtPBC_A_StkBCb`: S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
* `S4.Def_RP_EtPBC_A_StkBCc0`: S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2T4b =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4b): `thetaM_res`, classes with coefficients `clsD`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

end Theta

section ClsD

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

theorem clsD_comp {F : EtSh Λ P} {G G' : EtSh Λ (chEt c φ).left} (g : G' ⟶ G)
    (f : G ⟶ (res (chEt c φ).hom Λ).obj F) (Y : H Λ ((res (toD1 c φ a).left Λ).obj G') 1) :
    clsD c φ a hUz hS (g ≫ f) Y =
      clsD c φ a hUz hS f (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map g)) (add_zero 1)) := by
  rw [clsD_eq, clsD_eq, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Functor.map_comp, Category.assoc]

end ClsD

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBCb =====
section

/-!
# S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

variable (s)

/-- **The base change map on stalks** `Q_s → Ext^n(Λ_{P_s}, ι^* F)`. -/
def stalkBC (he : GermNat Λ g F n Q e) (x : ToType (s.point.presheafFiber.obj Q)) :
    Ext.{u} (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj F) n :=
  (isColimitOfPreserves (forget (ModuleCat.{u} Λ))
    (colimit.isColimit ((CategoryOfElements.π s.point.fiber).op ⋙ Q))).desc (stalkCocone s he) x

theorem stalkBC_germ (he : GermNat Λ g F n Q e) (X : S.Etale) (x : s.point.fiber.obj X) (z : Q.obj (op X)) :
    stalkBC s he (s.point.toPresheafFiber X x Q z) = germBC Λ g s F n Q e (s.point.fiber.elementsMk X x) z :=
  ConcreteCategory.congr_hom ((isColimitOfPreserves (forget (ModuleCat.{u} Λ))
    (colimit.isColimit ((CategoryOfElements.π s.point.fiber).op ⋙ Q))).fac
      (stalkCocone s he) (op (s.point.fiber.elementsMk X x))) z

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBCc0 =====
section

/-!
# S4-EtPBC-A, L1f part 3a: `stalkBC` is additive (`stalkBCHom`)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

variable (s)

theorem stalkBC_add (he : GermNat Λ g F n Q e) (x y : ToType (s.point.presheafFiber.obj Q)) :
    stalkBC s he (x + y) = stalkBC s he x + stalkBC s he y := by
  obtain ⟨X, x', z₁, z₂, rfl, rfl⟩ := s.point.toPresheafFiber_jointly_surjective₂ x y
  rw [← map_add, stalkBC_germ, stalkBC_germ, stalkBC_germ, map_add]

end RamanujanPetersson.EtPBC

end

end


