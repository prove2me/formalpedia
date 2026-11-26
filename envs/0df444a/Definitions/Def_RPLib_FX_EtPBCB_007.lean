-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_007
-- name    : RPLib_FX_EtPBCB_007
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T05:02:54.051328+00:00
-- url     : https://prove2.me/theorems/ea4a94ab-046d-5f59-b2f0-9a60deb6f45b
-- title:
--   Proper base change for iterated projective-line bundles, library file 007
-- statement:
--   File 007 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
--   * `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_006

/-!
# Proper base change for iterated projective-line bundles, library file 007

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_C2`: S4-EtPBC-B, C2 + C3: fibre vanishing for `P^1_Y ⟶ Y ⟶ S`
* `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
-/

set_option autoImplicit false

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

end V

section C3

variable (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ] [Finite Λ]
  (p : ℕ) [ExpChar K p] [PerfectRing K p] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ)
  (hΛ : ∀ x : Λ, (l ^ m) • x = 0) {Y S : Scheme.{0}} [IsNoetherian Y] (g : Y ⟶ S) [LocallyOfFiniteType g]
  (gS : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include p hl hΛ in
/-- **C3: fibre vanishing for the composite** `P^1_Y ⟶ Y ⟶ S` from fibre vanishing for `Y ⟶ S`. -/
theorem fibVan_comp (hv : FibVan Λ g s) : FibVan Λ (qV K (g ≫ gS) ≫ g) s := by
  intro I _ q β
  have : IsClosedImmersion s.pt := T3d.isClosedImmersion_of_isIso_comp gS s.pt
  have : IsClosedImmersion (fibι (qV K (g ≫ gS) ≫ g) s) := T3d.isClosedImmersion_fibι _ s
  have h0 := H_eq_zero_of_push (qV K (g ≫ gS)) _ (fun n => rDer_N_isZero K p l hl m hΛ g gS s I n) q
    (H_pushN_eq_zero K p g gS s hv I q) ((closedH Λ (fibι (qV K (g ≫ gS) ≫ g) s) _ (q + 1)).symm β)
  exact (AddEquiv.map_eq_zero_iff _).1 h0

end C3

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
/-- **C5 step**: `P^1_Y ⟶ Y ⟶ S` from `Y ⟶ S` proper. -/
theorem good_comp {Y S : Scheme.{0}} [IsNoetherian Y] (g : Y ⟶ S) [IsProper g]
    (gS : S ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]
    (hg : PBCGood Λ g s) : PBCGood Λ (qV K (g ≫ gS) ≫ g) s :=
  ⟨bcSurj_comp K p g gS s hg.1, fibVan_comp K p l hl m hΛ g gS s hg.2⟩

end Step

section Tower

end Tower

section Main

variable (K : Type) [Field K] [IsAlgClosed K] (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ] [Finite Λ]
  (p : ℕ) [ExpChar K p] [PerfectRing K p] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ)
  (hΛ : ∀ x : Λ, (l ^ m) • x = 0) {S : Scheme.{0}} [IsNoetherian S] (gS : S ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include p l hl m hΛ in
theorem good_towerP (n : ℕ) : PBCGood Λ (towerP K gS n).2 s := by
  induction n with
  | zero => exact good_qV K Λ p l hl m hΛ gS s
  | succ n ih => exact good_comp K Λ p l hl m hΛ (towerP K gS n).2 gS s ih

include p l hl m hΛ in
/-- **C6: proper base change for `(P^1)^{n+1}_S ⟶ S`** at a `K`-rational geometric point `s`. -/
theorem pbc_towerP (n : ℕ) (F : EtSh Λ (towerP K gS n).1) (q : ℕ) :
    Nonempty (ToType ((s.stalkF Λ).obj (((push (towerP K gS n).2 Λ).rightDerived q).obj F)) ≃+
      H Λ ((pull (fibι (towerP K gS n).2 s) Λ).obj F) q) :=
  pbc_of_good Λ (towerP K gS n).2 s (good_towerP K Λ p l hl m hΛ gS s n) F q

end Main

end RamanujanPetersson.EtPBC

end

end


