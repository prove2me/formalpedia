-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_080
-- name    : RPLib_FX_EtPBC_080
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:50:11.771466+00:00
-- url     : https://prove2.me/theorems/f4cfc20d-75c4-5095-8055-5094186859fd
-- title:
--   Proper base change for the projective line, library file 080
-- statement:
--   File 080 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L7c1`: S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071

/-!
# Proper base change for the projective line, library file 080

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L7c1`: S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L7c1 =====
section

/-!
# S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
* `TrEh`: `TrE` as an additive map (built from `Ext.bilinearComp` and `mapExtAddHom`, so `TrEh x = TrE x` is `rfl`);
* `isClosedImmersion_ιP`: `ιP : P¹_K ⟶ P¹_S` is a closed immersion (`ι = e ≫ ιP`, `e` an isomorphism);
* `isAffine_ιPW`: `ιP^*W` is affine for `W` affine;
* **`ptCls_bcImg`**: `TrE` of a point class of `Λ[ιP^*W]` is the base change of the family class `αZ` at `jG`
  (`ptCls_Db`, `σP_eq`, `TrE_mvTheta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section L7c1

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- `TrE` as an additive map: `TrEh x = TrE x` by `rfl`. -/
def TrEh (R : (PV K gS).Etale) :
    Ext.{0} (freeSh Λ (etId (P1 K))) (freeSh Λ ((etPull (ιP gS s)).obj R)) 2 →+
      Ext.{0} (unitSh Λ (fib (qV K gS) s)) ((pull (fibι (qV K gS) s) Λ).obj (freeSh Λ R)) 2 :=
  (Ext.bilinearComp _ _ _ 0 2 2 (zero_add 2) (Ext.mk₀ (uE gS s Λ))).comp
    (((Ext.bilinearComp _ _ _ 2 0 2 (add_zero 2)).flip (Ext.mk₀ (vE gS s Λ R))).comp
      ((pull (fibToP1 K gS s) Λ).mapExtAddHom _ _ 2))

end L7c1

end RamanujanPetersson.EtPBC.EtMV

end

end


