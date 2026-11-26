-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_004
-- name    : RPLib_FX_EtPBCB_004
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:39:09.931225+00:00
-- url     : https://prove2.me/theorems/51dc4e73-bbfa-59af-bf6d-40b5910a372a
-- title:
--   Proper base change for iterated projective-line bundles, library file 004
-- statement:
--   File 004 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_VanA`: S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)
--   * `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_223
import Definitions.Def_RPLib_FX_EtPBCB_001

/-!
# Proper base change for iterated projective-line bundles, library file 004

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_VanA`: S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)
* `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_B_VanA =====
section

/-!
# S4-EtPBC-B, A2: proper base change from vanishing on injectives (effaceability)

Abstract `δ`-functor setting of `Delta`:
* **`Delta.surjAt_of_vanish`**: if base change is surjective on germs in degree `0` for every object and
  `Ext^(q+1)(B, L I) = 0` for every injective `I`, then it is surjective on germs in every degree.

Sheaves (`g : P ⟶ S`, `s` a geometric point of `S`):
* `FibVan Λ g s`: `H^(q+1)(P_s, I|P_s) = 0` for every injective `I` on `P`;
* **`pbc_of_van`**: for `g` universally closed, `BCSurj 0` + `FibVan` give `(R^q g_* F)_s ≃ H^q(P_s, F|P_s)`;
* **`van_of_pbc`**: conversely proper base change gives `FibVan`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- Surjectivity on germs in every degree from degree `0` and `FibVan`. -/
theorem bcSurj_of_van (h0 : ∀ G, BCSurj Λ g s 0 G) (hv : FibVan Λ g s) (q : ℕ) (G : EtSh Λ P) :
    BCSurj Λ g s q G :=
  Delta.surjAt_of_vanish h0 hv q G

/-- **Proper base change from `BCSurj 0` and `FibVan`.** -/
theorem pbc_of_van [UniversallyClosed g] (h0 : ∀ G, BCSurj Λ g s 0 G) (hv : FibVan Λ g s)
    (F : EtSh Λ P) (q : ℕ) :
    Nonempty (ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F)) ≃+
      H Λ ((pull (fibι g s) Λ).obj F) q) :=
  pbc_of_germs Λ g s (fun G => bcInj_zero Λ g s G) (bcSurj_of_van Λ g s h0 hv) F q

/-- **`FibVan` from proper base change.** -/
theorem van_of_pbc (h : ∀ (F : EtSh Λ P) (q : ℕ),
    Nonempty (ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F)) ≃+
      H Λ ((pull (fibι g s) Λ).obj F) q)) : FibVan Λ g s := by
  intro I _ q β
  obtain ⟨e⟩ := h I (q + 1)
  have hz : IsZero ((s.stalkF Λ).obj (((push g Λ).rightDerived (q + 1)).obj I)) :=
    (s.stalkF Λ).map_isZero ((push g Λ).isZero_rightDerived_obj_injective_succ q I)
  have : Subsingleton (ToType ((s.stalkF Λ).obj (((push g Λ).rightDerived (q + 1)).obj I))) :=
    ModuleCat.subsingleton_of_isZero hz
  exact e.symm.injective (Subsingleton.elim _ _)

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

end Good

section Step

variable (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] [Finite Λ]
  (p : ℕ) [ExpChar K p] [PerfectRing K p] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ)
  (hΛ : ∀ x : Λ, (l ^ m) • x = 0)

include p l hl m hΛ in
/-- **C5 base**: `P^1_S ⟶ S`. -/
theorem good_qV {S : Scheme.{0}} [IsNoetherian S] (gS : S ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)] : PBCGood Λ (qV K gS) s :=
  ⟨fun G => GenGeo.bcSurj_zero_qV K p gS s G, van_of_pbc Λ (qV K gS) s (pbc_P1 K p l hl m hΛ gS s)⟩

end Step

section Tower

end Tower

section Main

end Main

end RamanujanPetersson.EtPBC

end

end


