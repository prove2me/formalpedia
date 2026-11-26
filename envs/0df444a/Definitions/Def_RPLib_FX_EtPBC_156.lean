-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_156
-- name    : RPLib_FX_EtPBC_156
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:31:10.033799+00:00
-- url     : https://prove2.me/theorems/43cc242a-2c8c-573a-860c-e6954e53213a
-- title:
--   Proper base change for the projective line, library file 156
-- statement:
--   File 156 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_148

/-!
# Proper base change for the projective line, library file 156

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L7b2 =====
section

/-!
# S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
**`TrE_mvTheta`**: for an MV square over `qV^*V` on `P = P¹_K ×_K S` and a `K`-point `v'` of `V` over `s`, the
transport `TrE` of the `P¹_K`-class `Λ[σG] ∘ ιP^*(ε ∘ θ(p₁, κ) ∘ Λ[r])` is the base change at `jG = (V, v')` of the
family class `ε ∘ θ(p₁, κ) ∘ Λ[r]`. Proof: `mvThetaR_pull` along `e`, `bc_mvThetaR` at `jG`, and `mvTheta_map` along
the base change identifications `isoE` (`nbhdSec_eq`, `isoE_natural`, `isoE_left_fW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe w v₀ u₀

section GenTr

universe w' v₁ u₁ v₂ u₂

end GenTr

section TrMV

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]
  (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s)

variable {W' W U R : (PV K gS).Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ (etPull (qV K gS)).obj V}
  {v : U ⟶ (etPull (qV K gS)).obj V} {hsq : p₁ ≫ w = p₂ ≫ v}

theorem TrE_mvThetaR_lhs2 (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact) (r : W ⟶ R) (κ : H Λ (unitSh Λ W'.left) 1) :
    (Ext.mk₀ ((unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫
      (etPull (fibToP1 K gS s)).map (σG gS s V v' hv')))).comp
      (((Ext.mk₀ (pullFreeHom Λ (fibToP1 K gS s) _)).comp
        (((mvPull_shortExact (ιP gS s) hS).extClass.comp ((thetaM Λ ((etPull (ιP gS s)).map p₁) 1
          (pullH Λ (fW (ιP gS s) W') 1 κ)).comp (Ext.mk₀ (freeMap Λ ((etPull (ιP gS s)).map r))) (add_zero 1))
          (show 1 + 1 = 2 from rfl)).mapExactFunctor (pull (fibToP1 K gS s) Λ)) (zero_add 2)).comp
        (Ext.mk₀ (vE gS s Λ R)) (add_zero 2)) (zero_add 2) =
    (Ext.mk₀ ((unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫
      (etPull (fibToP1 K gS s)).map (σG gS s V v' hv')))).comp
      ((mvPull_shortExact (fibToP1 K gS s) (mvPull_shortExact (ιP gS s) hS)).extClass.comp
        ((thetaM Λ ((etPull (fibToP1 K gS s)).map ((etPull (ιP gS s)).map p₁)) 1
          (pullH Λ (fW (fibToP1 K gS s) ((etPull (ιP gS s)).obj W')) 1 (pullH Λ (fW (ιP gS s) W') 1 κ))).comp
          (Ext.mk₀ (freeMap Λ ((etPull (fibToP1 K gS s)).map ((etPull (ιP gS s)).map r) ≫ isoE gS s R) ≫
            pullFreeHom Λ (fibι (qV K gS) s) R)) (add_zero 1))
        (show 1 + 1 = 2 from rfl)) (zero_add 2)  := by
  have hP := mvThetaR_pull (fibToP1 K gS s) (mvPull_shortExact (ιP gS s) hS)
    (mvPull_shortExact (fibToP1 K gS s) (mvPull_shortExact (ιP gS s) hS)) ((etPull (ιP gS s)).map p₁)
    ((etPull (ιP gS s)).map r) (pullH Λ (fW (ιP gS s) W') 1 κ)
  rw [hP, ← cls_tail, vE_tail]

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end


