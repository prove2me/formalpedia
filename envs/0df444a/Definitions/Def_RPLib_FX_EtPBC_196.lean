-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_196
-- name    : RPLib_FX_EtPBC_196
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:50:36.611492+00:00
-- url     : https://prove2.me/theorems/4de516fe-1b22-5cdf-96b4-fa7ba65a5bc3
-- title:
--   Proper base change for the projective line, library file 196
-- statement:
--   File 196 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L7c1`: S4-EtPBC-A, O2 L7c1: the transport `TrE` as an additive map; point classes transport into germs
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_080
import Definitions.Def_RPLib_FX_EtPBC_168
import Definitions.Def_RPLib_FX_EtPBC_188

/-!
# Proper base change for the projective line, library file 196

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

/-- **Point classes transport into germs.** -/
theorem ptCls_bcImg {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0) (W : (PV K gS).Etale)
    (c : A1 K ⟶ P1 K) [IsOpenImmersion c]
    (x : Ext.{0} (freeSh Λ (etId (P1 K))) (freeSh Λ ((etPull (ιP gS s)).obj W)) 2)
    (hx : PtCls Λ c hN hΛ ((etPull (ιP gS s)).obj W) x) :
    TrEh gS s Λ W x ∈ Delta.bcImg (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s)
      (unitSh Λ (fib (qV K gS) s)) (bcUnit Λ (qV K gS) s) (bcUnit_comp Λ (qV K gS) s) (freeSh Λ W) 2 := by
  obtain ⟨a, B, φ, hEt, Uz', hUz, hS, s', c', -, hDed, ht, hPr, hUz', rfl⟩ := hx
  refine ⟨jG gS s (Vs (σz K gS (zc c a) (chart_hclA c a)) W) (v' gS s c a W φ ht hPr s')
    (v'_hom gS s c a W φ ht hPr s'), αZ gS c a W hN Λ hΛ c', ?_⟩
  show _ = TrE gS s Λ W _
  rw [ptCls_Db gS s c a W φ ht hPr s' Uz' hUz' hN Λ hΛ hUz hS c'
    (mvPull_shortExact (ιP gS s) (mvZ_shortExact K gS (zc c a) (chart_hclA c a) W (Qc gS c) Λ (hQc gS c a))),
    σP_eq]
  exact (TrE_mvTheta gS s Λ (Vs (σz K gS (zc c a) (chart_hclA c a)) W) (v' gS s c a W φ ht hPr s')
    (v'_hom gS s c a W φ ht hPr s')
    (mvZ_shortExact K gS (zc c a) (chart_hclA c a) W (Qc gS c) Λ (hQc gS c a)) (rW gS c a W)
    (κZ gS c a W hN Λ hΛ c')).symm

end L7c1

end RamanujanPetersson.EtPBC.EtMV

end

end


