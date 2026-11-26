-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_223
-- name    : RPLib_FX_EtPBC_223
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:30:08.416623+00:00
-- url     : https://prove2.me/theorems/b5541797-df2c-5785-8787-9eee64d186b0
-- title:
--   Proper base change for the projective line, library file 223
-- statement:
--   File 223 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8c`: S4-EtPBC-A, O2 L8c: degree-2 base change for every sheaf on `P¹_S`; proper base change for `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_222

/-!
# Proper base change for the projective line, library file 223

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L8c`: S4-EtPBC-A, O2 L8c: degree-2 base change for every sheaf on `P¹_S`; proper base change for `P¹_S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L8c =====
section

/-!
# S4-EtPBC-A, O2 L8c: degree-2 base change for every sheaf on `P¹_S`; proper base change for `P¹_S`
* `trG_isLoc_mem`: one-point classes transport into germs (`isLoc_aff`, `kill_lift`, `TrG_natural`);
* **`bcSurj_two_PV`**: `BCSurj 2` for every sheaf on `P¹_S` (`mem_locSpan_P1`, `TrG_surjective`);
* **`pbc_P1`**: proper base change for `P¹_S` at a `K`-rational geometric point (`pbc_p1_of_surj`, `bcSurj_one_PV`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section TrG

end TrG

end RamanujanPetersson.EtPBC.EtMV

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

/-- **Proper base change for `P¹_S`** at a geometric point `s` with `s ≫ g_K` an isomorphism: for every sheaf `F`
of `Λ`-modules (`Λ` finite, killed by `l ^ m`, `l` invertible in `K`), the stalk at `s` of `R^q (qV)_* F` is
`H^q` of the fibre with coefficients in `ι^* F`. -/
theorem pbc_P1 (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ] [Finite Λ]
    (p : ℕ) [ExpChar K p] [PerfectRing K p] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ)
    (hΛ : ∀ x : Λ, (l ^ m) • x = 0) {S : Scheme.{0}} [IsNoetherian S] (gS : S ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType gS] (s : GeomPt S) [IsIso (s.pt ≫ gS)] (F : EtSh Λ (PV K gS)) (q : ℕ) :
    Nonempty (ToType ((s.stalkF Λ).obj (((push (qV K gS) Λ).rightDerived q).obj F)) ≃+
      H Λ ((pull (fibι (qV K gS) s) Λ).obj F) q) :=
  have hΛ' : ((l ^ m : ℕ) : Λ) = 0 := (nsmul_one (l ^ m)).symm.trans (hΛ 1)
  pbc_p1_of_surj K l hl m hΛ' gS s p (fun G => bcSurj_one_PV K gS s p G)
    (fun G => EtMV.bcSurj_two_PV gS s Λ l hl m hΛ G) F q

end RamanujanPetersson.EtPBC

end

end


