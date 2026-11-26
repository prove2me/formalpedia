-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_006
-- name    : RPLib_FX_EtPBCB_006
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:46:27.430981+00:00
-- url     : https://prove2.me/theorems/ed6a8802-155e-5b9a-b147-8446a76f8c48
-- title:
--   Proper base change for iterated projective-line bundles, library file 006
-- statement:
--   File 006 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
--   * `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
--   * `S4.Def_RP_EtPBC_B_BC0`: S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_003
import Definitions.Def_RPLib_FX_EtPBCB_005

/-!
# Proper base change for iterated projective-line bundles, library file 006

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
* `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
* `S4.Def_RP_EtPBC_B_BC0`: S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_B_NatZ =====
section

/-!
# S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test

* `sec0Ext_natural`, `stalkBC0_natural`, **`stalkEquiv0_natural`**: the degree-0 stalk base change equivalence
  `(g_* F)_s̄ ≃ H^0(P_s̄, ι^* F)` is natural in `F`;
* **`bijective_stalk_push`**: if `ι^* φ` is an isomorphism, `(g_* φ)_s̄` is bijective (given the degree-0 germ
  conditions); **`bijective_stalk_push_qV`** for `P^1_V ⟶ V` at a `K`-rational point;
* **`isIso_of_closed`**: on `X` locally of finite type over a field, a map of sheaves whose stalk maps at the closed
  points are bijective is an isomorphism (Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Nat

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Naturality of the degree-0 stalk base change equivalence.** -/
theorem stalkEquiv0_natural {F F' : EtSh Λ P} (φ : F ⟶ F') (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F)
    (hI' : BCInj Λ g s 0 F') (hS' : BCSurj Λ g s 0 F')
    (x : ToType (s.point.presheafFiber.obj ((sheafToPresheaf _ _).obj ((push g Λ).obj F)))) :
    stalkEquiv s (sec0Ext_map Λ g F') hI' hS' ((s.point.presheafFiber.map ((push g Λ).map φ).hom).hom x) =
      (stalkEquiv s (sec0Ext_map Λ g F) hI hS x).comp (Ext.mk₀ ((pull (fibι g s) Λ).map φ)) (add_zero 0) := by
  change stalkEquivE s _ hI' hS' _ = (stalkEquivE s _ hI hS x).comp _ _
  rw [stalkEquivE_apply, stalkEquivE_apply]
  exact stalkBC0_natural Λ g s φ x

/-- **If `ι^* φ` is an isomorphism, the stalk map `(g_* φ)_s̄` is bijective.** -/
theorem bijective_stalk_push {F F' : EtSh Λ P} (φ : F ⟶ F') [IsIso ((pull (fibι g s) Λ).map φ)]
    (hI : BCInj Λ g s 0 F) (hS : BCSurj Λ g s 0 F) (hI' : BCInj Λ g s 0 F') (hS' : BCSurj Λ g s 0 F') :
    Function.Bijective ((s.stalkF Λ).map ((push g Λ).map φ)).hom := by
  change Function.Bijective (s.point.presheafFiber.map ((push g Λ).map φ).hom).hom
  have h : ∀ x, stalkEquiv s (sec0Ext_map Λ g F') hI' hS' ((s.point.presheafFiber.map ((push g Λ).map φ).hom).hom x) =
      Hiso Λ (asIso ((pull (fibι g s) Λ).map φ)) 0 (stalkEquiv s (sec0Ext_map Λ g F) hI hS x) := fun x =>
    (stalkEquiv0_natural Λ g s φ hI hS hI' hS' x).trans (extIsoRight_apply _ (asIso _) 0 _).symm
  have hb : Function.Bijective ((stalkEquiv s (sec0Ext_map Λ g F') hI' hS') ∘
      (s.point.presheafFiber.map ((push g Λ).map φ).hom).hom) := by
    rw [show (stalkEquiv s (sec0Ext_map Λ g F') hI' hS') ∘
        (s.point.presheafFiber.map ((push g Λ).map φ).hom).hom =
        (Hiso Λ (asIso ((pull (fibι g s) Λ).map φ)) 0) ∘ (stalkEquiv s (sec0Ext_map Λ g F) hI hS) from funext h]
    exact (Hiso Λ _ 0).bijective.comp (stalkEquiv s _ hI hS).bijective
  exact (Function.Bijective.of_comp_iff' (stalkEquiv s _ hI' hS').bijective _).1 hb

/-- `bijective_stalk_push` for `P^1_V ⟶ V` at a `K`-rational point. -/
theorem bijective_stalk_push_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    [IsNoetherianRing Λ] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) [IsNoetherian V]
    [LocallyOfFiniteType gV] (t : GeomPt V) [IsIso (t.pt ≫ gV)] {F F' : EtSh Λ (PV K gV)} (φ : F ⟶ F')
    [IsIso ((pull (fibι (qV K gV) t) Λ).map φ)] :
    Function.Bijective ((t.stalkF Λ).map ((push (qV K gV) Λ).map φ)).hom :=
  bijective_stalk_push Λ (qV K gV) t φ (bcInj_zero Λ (qV K gV) t F) (GenGeo.bcSurj_zero_qV K p gV t F)
    (bcInj_zero Λ (qV K gV) t F') (GenGeo.bcSurj_zero_qV K p gV t F')

end Nat

section Closed

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_C2 =====
section

/-!
# S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`

`h = qV K gY : X = P^1_Y ⟶ Y` (`gY = g ≫ gS`), `f = h ≫ g`, `s` a `K`-rational point of `S`,
`ι_X : X_s ⟶ X`, `ι_Y : Y_s ⟶ Y`, `h' : X_s ⟶ Y_s`, `N = ι_X* ι_X^* I`:
* `fibCompH`, `fibCompH_ι`, `pushNIso`: `h_* ι_X* G ≅ ι_Y* h'_* G`;
* `isIso_pullFib_unit`, `isIso_pullt_unit`: `ι_t^*` of the unit `I ⟶ N` is an isomorphism if `X_t ⟶ X` factors
  through `X_s`;
* **`isIso_v`**: `ι_Y^* (h_* I) ⟶ ι_Y^* (h_* N)` is an isomorphism (closed points of `Y_s`, `NatZ`);
* **`H_pushN_eq_zero`**: `H^(n+1)(Y, h_* N) = 0` if `g` has fibre vanishing at `s` (`I` injective);
* **`fibVan_comp`** (C3): fibre vanishing for `f = h ≫ g` at `s` (C1 + degenerate Leray + closed pushforward).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Gen

end Gen

section V

variable (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [ExpChar K p] [PerfectRing K p] {Λ : Type u}
  [CommRing Λ] [IsNoetherianRing Λ] {Y S : Scheme.{u}} [IsNoetherian Y] (g : Y ⟶ S) [LocallyOfFiniteType g]
  (gS : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include p in
/-- **`ι_Y^* (h_* I) ≅ ι_Y^* (h_* N)`** via the unit `I ⟶ N`. -/
theorem isIso_v (I : EtSh Λ (PV K (g ≫ gS))) :
    IsIso ((pull (fibι g s) Λ).map ((push (qV K (g ≫ gS)) Λ).map
      ((pullAdj (fibι (qV K (g ≫ gS) ≫ g) s) Λ).unit.app I))) := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι g s) := T3d.isClosedImmersion_fibι g s
  have : IsClosedImmersion (fibι (qV K (g ≫ gS) ≫ g) s) := T3d.isClosedImmersion_fibι _ s
  refine isIso_of_closed (fibι g s ≫ g ≫ gS) _ fun y hy => ?_
  have hy' := isIso_geomPtAt (fibι g s ≫ g ≫ gS) y hy
  have e : ((geomPtAt y).map (fibι g s)).pt ≫ (g ≫ gS) = (geomPtAt y).pt ≫ (fibι g s ≫ g ≫ gS) :=
    Category.assoc _ _ _
  have : IsIso (((geomPtAt y).map (fibι g s)).pt ≫ (g ≫ gS)) := by rw [e]; exact hy'
  have ha : ((geomPtAt y).map (fibι g s)).pt ≫ g = ((geomPtAt y).pt ≫ pullback.snd g s.pt) ≫ s.pt := by
    change ((geomPtAt y).pt ≫ pullback.fst g s.pt) ≫ g = _
    rw [Category.assoc, pullback.condition, Category.assoc]
  have := isIso_pullt_unit (qV K (g ≫ gS)) g s ((geomPtAt y).map (fibι g s)) _ ha I
  have hb := bijective_stalk_push_qV Λ K p (g ≫ gS) ((geomPtAt y).map (fibι g s))
    ((pullAdj (fibι (qV K (g ≫ gS) ≫ g) s) Λ).unit.app I)
  have nat := (pullStalkIso (fibι g s) Λ (geomPtAt y)).hom.naturality
    ((push (qV K (g ≫ gS)) Λ).map ((pullAdj (fibι (qV K (g ≫ gS) ≫ g) s) Λ).unit.app I))
  have hc : Function.Bijective ((pull (fibι g s) Λ ⋙ (geomPtAt y).stalkF Λ).map
      ((push (qV K (g ≫ gS)) Λ).map ((pullAdj (fibι (qV K (g ≫ gS) ≫ g) s) Λ).unit.app I)) ≫
        (pullStalkIso (fibι g s) Λ (geomPtAt y)).hom.app _).hom := by
    rw [nat, ModuleCat.hom_comp]
    exact hb.comp ((pullStalkIso (fibι g s) Λ (geomPtAt y)).app _).toLinearEquiv.bijective
  rw [ModuleCat.hom_comp] at hc
  exact (Function.Bijective.of_comp_iff'
    ((pullStalkIso (fibι g s) Λ (geomPtAt y)).app _).toLinearEquiv.bijective _).1 hc

include p in
/-- **`H^(n+1)(Y, h_* N) = 0`** from fibre vanishing for `g` (`I` injective). -/
theorem H_pushN_eq_zero (hv : FibVan Λ g s) (I : EtSh Λ (PV K (g ≫ gS))) [Injective I] (n : ℕ)
    (β : H Λ ((push (qV K (g ≫ gS)) Λ).obj ((push (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj
      ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I))) (n + 1)) : β = 0 := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι g s) := T3d.isClosedImmersion_fibι g s
  have := isIso_v K p g gS s I
  have e1 := pushNIso (qV K (g ≫ gS)) g s ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I)
  have e2 : (push (fibCompH (qV K (g ≫ gS)) g s) Λ).obj ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I) ≅
      (pull (fibι g s) Λ).obj ((push (qV K (g ≫ gS)) Λ).obj I) :=
    (asIso ((pullAdj (fibι g s) Λ).counit.app _)).symm ≪≫ (pull (fibι g s) Λ).mapIso e1.symm ≪≫
      (asIso ((pull (fibι g s) Λ).map ((push (qV K (g ≫ gS)) Λ).map
        ((pullAdj (fibι (qV K (g ≫ gS) ≫ g) s) Λ).unit.app I)))).symm
  have h1 := hv ((push (qV K (g ≫ gS)) Λ).obj I) n
    (Hiso Λ e2 (n + 1) (closedH Λ (fibι g s) _ (n + 1) (Hiso Λ e1 (n + 1) β)))
  exact (AddEquiv.map_eq_zero_iff _).1 ((AddEquiv.map_eq_zero_iff _).1 ((AddEquiv.map_eq_zero_iff _).1 h1))

end V

section C3

end C3

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_BC0 =====
section

/-!
# S4-EtPBC-B, C4: degree-0 base change surjectivity for `P^1_Y ⟶ Y ⟶ S`

* `bcSurj_comp_of_iso`: for `f = h ≫ g`, if the base change map `vMapG : ιY^* h_* I ⟶ h'_* ιX^* I` is an
  isomorphism and `BCSurj 0` holds for `g` at `h_* I`, then `BCSurj 0` holds for `f` at `I`
  (`bcUnit_psi` + naturality of `sqQ` + the mate identity `mateG`);
* `isIso_vMap_qV`: `vMapG` is an isomorphism for `h = qV K (g ≫ gS)` (`isIso_v`);
* **`bcSurj_comp`**: `BCSurj 0` for `qV K (g ≫ gS) ≫ g` from `BCSurj 0` for `g` (all sheaves, via an
  injective envelope and `bcSurj_of_mono`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.Mate RamanujanPetersson.EtPBC.Z3

universe u

section Gen

end Gen

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [ExpChar K p] [PerfectRing K p] {Λ : Type u}
  [CommRing Λ] [IsNoetherianRing Λ] {Y S : Scheme.{u}} [IsNoetherian Y] (g : Y ⟶ S) [LocallyOfFiniteType g]
  (gS : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include p in
theorem isIso_vMap_qV (I : EtSh Λ (PV K (g ≫ gS))) :
    IsIso (vMapG (fibι (qV K (g ≫ gS) ≫ g) s) (fibι g s) (qV K (g ≫ gS)) (fibCompH (qV K (g ≫ gS)) g s)
      (fibCompH_ι (qV K (g ≫ gS)) g s) I) := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι g s) := T3d.isClosedImmersion_fibι g s
  have : IsIso ((pull (fibι g s) Λ).map ((push (qV K (g ≫ gS)) Λ).map
      (unitN (fibι (qV K (g ≫ gS) ≫ g) s) I))) := isIso_v K p g gS s I
  simp only [vMapG, CategoryTheory.Functor.map_comp]
  infer_instance

include p in
/-- **C4: `BCSurj 0` for `P^1_Y ⟶ Y ⟶ S`** from `BCSurj 0` for `Y ⟶ S`. -/
theorem bcSurj_comp [UniversallyClosed (qV K (g ≫ gS) ≫ g)] (hg : ∀ G, BCSurj Λ g s 0 G)
    (G : EtSh Λ (PV K (g ≫ gS))) : BCSurj Λ (qV K (g ≫ gS) ≫ g) s 0 G := by
  have := isIso_vMap_qV K p g gS s (Injective.under G)
  exact bcSurj_of_mono (qV K (g ≫ gS) ≫ g) s (Injective.ι G)
    (bcSurj_comp_of_iso (qV K (g ≫ gS)) g s (Injective.under G) (hg _))

end P1

end RamanujanPetersson.EtPBC

end

end


