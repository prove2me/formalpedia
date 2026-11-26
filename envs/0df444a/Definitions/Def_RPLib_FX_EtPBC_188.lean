-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_188
-- name    : RPLib_FX_EtPBC_188
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:15:11.068923+00:00
-- url     : https://prove2.me/theorems/4031934e-6882-5180-8b42-bb92b3da606f
-- title:
--   Proper base change for the projective line, library file 188
-- statement:
--   File 188 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_171
import Definitions.Def_RPLib_FX_EtPBC_183

/-!
# Proper base change for the projective line, library file 188

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2L6c1 =====
section

/-!
# S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square

For the data of a point class `x = pcD c' ∘ Λ[s']` with coefficients `T = ιP^* W`:
* `pcD_s'`: `x = ε(locC D) ∘ θ(prW, κ_D) ∘ Λ[s']`, `κ_D = isoT⁻¹^* toWa^* ξ`;
* `shrink_Db`: the same class through `D♭ = opn D Vb`;
* `hrM : aM ≫ ιP^*(rW) = opnι ≫ s'`, `hmapA`, `hκ` (the Kummer classes agree on `D♭ ×_P Uz'`);
* **`ptCls_Db`**: `x = Λ[σP] ∘ (ιP^*MVZ-class of fW^* κZ and ιP^* rW)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Cls

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)
  {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)
  (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz' ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz')).ShortExact) (c' : Λ)

include hUz' in
/-- **A point class through the family square**: `x = Λ[σP] ∘ (ιP^*MVZ-class)`. -/
theorem ptCls_Db
    {hsq₂ : (etPull (ιP gS s)).map
        (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) ≫
      (etPull (ιP gS s)).map (wz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) =
      (etPull (ιP gS s)).map (p₂z K gS (zc c a) (chart_hclA c a) W (Qc gS c)) ≫
      (etPull (ιP gS s)).map
        (prW (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a))))}
    (hS₂ : (mvC Λ _ _ _ _ hsq₂).ShortExact) :
    (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s')) (add_zero 2) =
      (Ext.mk₀ (freeMap Λ (σP gS s c a W (v' gS s c a W φ ht hP s') (v'_hom gS s c a W φ ht hP s')))).comp
        (hS₂.extClass.comp ((thetaM Λ ((etPull (ιP gS s)).map
          (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a))))) 1
            (pullH Λ (fW (ιP gS s) (DzO gS c a W)) 1 (κZ gS c a W hN Λ hΛ c'))).comp
              (Ext.mk₀ (freeMap Λ ((etPull (ιP gS s)).map (rW gS c a W)))) (add_zero 1))
          (show 1 + 1 = 2 from rfl)) (zero_add 2) := by
  refine (pcD_s' gS s c a W φ s' Uz' hN Λ hΛ hUz hS c').trans
    ((shrink_Db gS s c a W φ ht hP s' Uz' hUz' Λ hS _).trans (Eq.trans ?_
      (mvTheta_Db gS s c a W φ ht hP s' Uz' hUz' Λ hS₂ _ _).symm))
  rw [hκ gS s c a W φ ht hP s' Uz' hUz' hN Λ hΛ hUz c', hrM gS s c a W φ ht hP s']

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end

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

/-- **Transport of a family MV-theta class**: `TrE` of the `P¹_K`-class is the base change at `jG`. -/
theorem TrE_mvTheta (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact) (r : W ⟶ R) (κ : H Λ (unitSh Λ W'.left) 1) :
    TrE gS s Λ R ((Ext.mk₀ (freeMap Λ (σG gS s V v' hv'))).comp
      ((mvPull_shortExact (ιP gS s) hS).extClass.comp ((thetaM Λ ((etPull (ιP gS s)).map p₁) 1
        (pullH Λ (fW (ιP gS s) W') 1 κ)).comp (Ext.mk₀ (freeMap Λ ((etPull (ιP gS s)).map r))) (add_zero 1))
          (show 1 + 1 = 2 from rfl)) (zero_add 2)) =
    Delta.bc (pull (fibι (qV K gS) s) Λ) (nbhdSys Λ (qV K gS) s) (unitSh Λ (fib (qV K gS) s))
      (bcUnit Λ (qV K gS) s) (jG gS s V v' hv') (freeSh Λ R) 2
      (hS.extClass.comp ((thetaM Λ p₁ 1 κ).comp (Ext.mk₀ (freeMap Λ r)) (add_zero 1)) (show 1 + 1 = 2 from rfl)) :=
  TrE_mvThetaR gS s Λ V v' hv' hS r κ

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end


