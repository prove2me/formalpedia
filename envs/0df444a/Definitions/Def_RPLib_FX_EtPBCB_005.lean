-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_005
-- name    : RPLib_FX_EtPBCB_005
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:41:34.018861+00:00
-- url     : https://prove2.me/theorems/206c5117-44e8-5b33-852b-76147560d576
-- title:
--   Proper base change for iterated projective-line bundles, library file 005
-- statement:
--   File 005 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
--   * `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
--   * `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_002
import Definitions.Def_RPLib_FX_EtPBCB_004

/-!
# Proper base change for iterated projective-line bundles, library file 005

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
* `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
* `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_B_C1 =====
section

/-!
# S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish

For `h = qV K gY : PV K gY ⟶ Y` (`gY = g ≫ gS`), `f = h ≫ g`, a `K`-rational point `s` of `S`, the closed
fibre inclusion `ι : X_s ⟶ X` of `f` and an injective sheaf `I` on `X = PV K gY`:
* `fibMap`, `fibMap_ι`: if `t.pt ≫ g = a ≫ s.pt`, the fibre `X_t` of `h` maps to `X_s` over `X`;
* `pullNIso`: then `ι_t^* ι_* ι^* I ≅ ι_t^* I` (closed counit);
* `isZero_pull_push`: if `g t̄ ≠ s̄`, `ι_t^* ι_* G = 0` (stalks);
* **`rDer_N_isZero`**: `R^(n+1) h_* (ι_* ι^* I) = 0` (closed points of `Y` + `pbc_P1` + Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Fib

section Map

end Map

end Fib

section C1

variable (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ] [Finite Λ]
  (p : ℕ) [ExpChar K p] [PerfectRing K p] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ)
  (hΛ : ∀ x : Λ, (l ^ m) • x = 0) {Y S : Scheme.{0}} [IsNoetherian Y] (g : Y ⟶ S) [LocallyOfFiniteType g]
  (gS : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include p hl hΛ in
/-- **C1**: `R^(n+1) h_* (ι_* ι^* I) = 0` for injective `I`. -/
theorem rDer_N_isZero (I : EtSh Λ (PV K (g ≫ gS))) [Injective I] (n : ℕ) :
    IsZero (((push (qV K (g ≫ gS)) Λ).rightDerived (n + 1)).obj
      ((push (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I))) := by
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι (qV K (g ≫ gS) ≫ g) s) := T3d.isClosedImmersion_fibι _ s
  refine isZero_of_closed (g ≫ gS) _ (fun y hy => ?_)
  have := isIso_geomPtAt (g ≫ gS) y hy
  change IsZero (((geomPtAt y).stalkF Λ).obj _)
  obtain ⟨e⟩ := pbc_P1 K p l hl m hΛ (g ≫ gS) (geomPtAt y)
    ((push (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I)) (n + 1)
  have hz : ∀ β : H Λ ((pull (fibι (qV K (g ≫ gS)) (geomPtAt y)) Λ).obj
      ((push (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj ((pull (fibι (qV K (g ≫ gS) ≫ g) s) Λ).obj I))) (n + 1),
      β = 0 := by
    by_cases hc : g y = s.center
    · have hst : ((geomPtAt y).map g).center = s.center := by
        rw [GeomPt.center_map, center_geomPtAt]; exact hc
      have ha := pt_factor_of_center gS s ((geomPtAt y).map g) hst
      have hv := van_of_pbc Λ (qV K (g ≫ gS)) (geomPtAt y)
        (fun F q => pbc_P1 K p l hl m hΛ (g ≫ gS) (geomPtAt y) F q)
      intro β
      exact (AddEquiv.map_eq_zero_iff _).1
        (hv I n ((Hiso Λ (pullNIso (qV K (g ≫ gS)) g s (geomPtAt y) _ ha I) (n + 1)) β))
    · exact H_eq_zero_of_isZero (isZero_pull_push _ g s (geomPtAt y)
        (by rwa [center_geomPtAt]) _) (n + 1)
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => e.injective ?_⟩
  rw [hz (e a), hz (e b)]

end C1

end RamanujanPetersson.EtPBC

end

end

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

theorem stalkBC0_natural {F F' : EtSh Λ P} (φ : F ⟶ F')
    (x : ToType (s.point.presheafFiber.obj ((sheafToPresheaf _ _).obj ((push g Λ).obj F)))) :
    stalkBC s (sec0Ext_map Λ g F') ((s.point.presheafFiber.map ((push g Λ).map φ).hom).hom x) =
      (stalkBC s (sec0Ext_map Λ g F) x).comp (Ext.mk₀ ((pull (fibι g s) Λ).map φ)) (add_zero 0) := by
  obtain ⟨T, a, z, rfl⟩ := s.point.toPresheafFiber_jointly_surjective x
  have key : (s.point.presheafFiber.map ((push g Λ).map φ).hom).hom
      (s.point.toPresheafFiber T a ((sheafToPresheaf _ _).obj ((push g Λ).obj F)) z) =
      s.point.toPresheafFiber T a ((sheafToPresheaf _ _).obj ((push g Λ).obj F'))
        ((((push g Λ).map φ).hom.app (op T)).hom z) :=
    congrArg (fun χ => χ.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality
      (Φ := s.point) ((push g Λ).map φ).hom T a)
  rw [key, stalkBC_germ, stalkBC_germ]
  show Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s)
      (s.point.fiber.elementsMk T a) F' 0 (sec0Ext Λ g F' T ((((push g Λ).map φ).hom.app (op T)).hom z)) =
    (Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s)
      (s.point.fiber.elementsMk T a) F 0 (sec0Ext Λ g F T z)).comp
        (Ext.mk₀ ((pull (fibι g s) Λ).map φ)) (add_zero 0)
  rw [sec0Ext_natural]
  exact Delta.bc_comp_mk₀ (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s)
    (s.point.fiber.elementsMk T a) φ 0 (sec0Ext Λ g F T z)

end Nat

section Closed

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Tower =====
section

/-!
# S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line

* `PBCGood Λ g s`: `BCSurj 0` for every sheaf plus fibre vanishing `FibVan`; it gives proper base change
  in all degrees for `g` universally closed (`pbc_of_good`);
* `good_qV`: `P^1_S ⟶ S` (`bcSurj_zero_qV` + `pbc_P1`);
* `good_comp`: `PBCGood g ⟹ PBCGood (P^1_Y ⟶ Y ⟶ S)` for `g` proper (`bcSurj_comp` + `fibVan_comp`);
* `towerP K gS n : Σ Y, Y ⟶ S` is `(P^1)^{n+1}_S` as an iterated `P^1`-bundle; **`pbc_towerP`**: proper
  base change `(R^q f_* F)_s ≃+ H^q(X_s, F|X_s)` for its structure map `f`, at `K`-rational `s`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

section Good

variable (Λ : Type u) [CommRing Λ] {Y S : Scheme.{u}} (g : Y ⟶ S) (s : GeomPt S)

/-- **Proper base change in all degrees** from `PBCGood`. -/
theorem pbc_of_good [UniversallyClosed g] (hg : PBCGood Λ g s) (F : EtSh Λ Y) (q : ℕ) :
    Nonempty (ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F)) ≃+
      H Λ ((pull (fibι g s) Λ).obj F) q) :=
  pbc_of_van Λ g s hg.1 hg.2 F q

end Good

section Step

end Step

section Tower

end Tower

section Main

end Main

end RamanujanPetersson.EtPBC

end

end


