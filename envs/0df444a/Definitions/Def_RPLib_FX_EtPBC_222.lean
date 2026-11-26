-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_222
-- name    : RPLib_FX_EtPBC_222
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T04:25:37.567128+00:00
-- url     : https://prove2.me/theorems/4bf61340-4026-5000-923c-59a881fad6a7
-- title:
--   Proper base change for the projective line, library file 222
-- statement:
--   File 222 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8c`: S4-EtPBC-A, O2 L8c: degree-2 base change for every sheaf on `P¹_S`; proper base change for `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_127
import Definitions.Def_RPLib_FX_EtPBC_221

/-!
# Proper base change for the projective line, library file 222

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

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- **Degree-2 base change for every sheaf on `P¹_S`** (`Λ` killed by `l ^ m`, `l` invertible in `K`). -/
theorem bcSurj_two_PV (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (m : ℕ) (hΛ : ∀ x : Λ, (l ^ m) • x = 0)
    (G : EtSh Λ (PV K gS)) : BCSurj Λ (qV K gS) s 2 G := by
  have : NeZero (l ^ m) := ⟨pow_ne_zero m (Fact.out : l.Prime).ne_zero⟩
  have hN : ((l ^ m : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero m hl
  have hΛ' : ((l ^ m : ℕ) : Λ) = 0 := (nsmul_one (l ^ m)).symm.trans (hΛ 1)
  have key : locSpan Λ ((pull (ιP gS s) Λ).obj G) ≤
      (Delta.bcImg (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s) (unitSh Λ (fib (qV K gS) s))
        (bcUnit Λ (qV K gS) s) (bcUnit_comp Λ (qV K gS) s) G 2).comap (TrGh gS s Λ G) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨z, hx⟩
    exact trG_isLoc_mem gS s Λ (fun H hH => bcSurj_two_fgt gS s Λ l hl m hN hΛ H hH) G z x hx
  intro β
  obtain ⟨x, rfl⟩ := TrG_surjective gS s Λ G β
  exact key (mem_locSpan_P1 K l hl m hΛ' _ x)

end TrG

end RamanujanPetersson.EtPBC.EtMV

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

end RamanujanPetersson.EtPBC

end

end


