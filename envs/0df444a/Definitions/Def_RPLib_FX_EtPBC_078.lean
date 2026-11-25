-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_078
-- name    : RPLib_FX_EtPBC_078
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:38:01.06109+00:00
-- url     : https://prove2.me/theorems/ad2a4338-3148-5f2c-b215-eb29b0b9e653
-- title:
--   Proper base change for the projective line, library file 078
-- statement:
--   File 078 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071

/-!
# Proper base change for the projective line, library file 078

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L8a =====
section

/-!
# S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
* **`Delta.surjAt_coprod`**: surjectivity on germs passes to finite coproducts (`ι : Type`, finite);
* `wGIso`, `wG`, `wG_natural`: `e^* ιP^* G ≅ ι^* G` (`e = fibToP1`, `e ≫ ιP = ι`), natural in `G`;
* **`TrG`** `G x = u ∘ e^*x ∘ wG`: `Ext²(Λ[P¹_K], ιP^*G) → Ext²(Λ_{P_s}, ι^*G)`; `TrGh` (additive, `rfl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

theorem wG_natural {H G : EtSh Λ (PV K gS)} (m : H ⟶ G) :
    (pull (fibToP1 K gS s) Λ).map ((pull (ιP gS s) Λ).map m) ≫ wG gS s Λ G =
      wG gS s Λ H ≫ (pull (fibι (qV K gS) s) Λ).map m :=
  ((pullCompIso Λ (fibToP1 K gS s) (ιP gS s)).inv ≫ (pullCongr Λ (fibToP1_ιP gS s)).hom).naturality m

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


