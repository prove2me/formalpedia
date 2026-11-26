-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_127
-- name    : RPLib_FX_EtPBC_127
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:20:15.224611+00:00
-- url     : https://prove2.me/theorems/1ca3c2f5-5f2d-5bf8-a6ca-c459e5e67cab
-- title:
--   Proper base change for the projective line, library file 127
-- statement:
--   File 127 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8c`: S4-EtPBC-A, O2 L8c: degree-2 base change for every sheaf on `P¹_S`; proper base change for `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_084
import Definitions.Def_RPLib_FX_EtPBC_089
import Definitions.Def_RPLib_FX_EtPBC_095
import Definitions.Def_RPLib_FX_EtPBC_113

/-!
# Proper base change for the projective line, library file 127

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

/-- **One-point classes transport into germs** once `BCSurj 2` holds for `FGT` sheaves. -/
theorem trG_isLoc_mem (hF : ∀ H : EtSh Λ (PV K gS), FGT Λ H → BCSurj Λ (qV K gS) s 2 H)
    (G : EtSh Λ (PV K gS)) (z : P1 K) (x : Ext.{0} (freeSh Λ (etId (P1 K))) ((pull (ιP gS s) Λ).obj G) 2)
    (hx : IsLoc Λ ((pull (ιP gS s) Λ).obj G) z x) :
    TrG gS s Λ G x ∈ Delta.bcImg (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s)
      (unitSh Λ (fib (qV K gS) s)) (bcUnit Λ (qV K gS) s) (bcUnit_comp Λ (qV K gS) s) G 2 := by
  obtain ⟨a, -, B, φ, hEt, -, hDed, -, -, Uo, Uz, h, hz, hD, hDn, hDr, κ, rfl⟩ :=
    isLoc_aff (p1Chart K z) hx ⟨_, p1Chart_p1Pt K z⟩
  have hUo := mem_Uo_iff (p1Chart K z) φ h hz hDr
  have hTA : IsAffine (prd (chEt (p1Chart K z) φ) (opEt Uo)).left := isAffine_prdUo (p1Chart K z) φ hUo
  obtain ⟨H, hH, m, κH, rfl⟩ := kill_lift gS s Λ (prd (chEt (p1Chart K z) φ) (opEt Uo)) G κ
  rw [← Ext.comp_assoc_of_third_deg_zero, TrG_natural]
  have hmem : ∀ y, (∃ (j : Nbhd s) (α : Ext.{0} ((nbhdSys Λ (qV K gS) s).obj j) H 2),
      Delta.bc (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s) (unitSh Λ (fib (qV K gS) s))
        (bcUnit Λ (qV K gS) s) j H 2 α = y) →
      y.comp (Ext.mk₀ ((pull (fibι (qV K gS) s) Λ).map m)) (add_zero 2) ∈ Delta.bcImg (pull (fibι (qV K gS) s) Λ)
        (nbhdSys Λ (qV K gS) s) (unitSh Λ (fib (qV K gS) s)) (bcUnit Λ (qV K gS) s)
        (bcUnit_comp Λ (qV K gS) s) G 2 := by
    rintro y ⟨j, α, rfl⟩
    exact ⟨j, α.comp (Ext.mk₀ m) (add_zero 2), Delta.bc_comp_mk₀ _ _ _ _ j m 2 α⟩
  exact hmem _ (hF H hH _)

end TrG

end RamanujanPetersson.EtPBC.EtMV

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

end RamanujanPetersson.EtPBC

end

end


