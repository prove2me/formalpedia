-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_183
-- name    : RPLib_FX_EtPBC_183
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:13:01.035128+00:00
-- url     : https://prove2.me/theorems/c98f8599-bfe5-5535-ad2d-6b2bca6bb9a6
-- title:
--   Proper base change for the projective line, library file 183
-- statement:
--   File 183 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_Inj0d1`: S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
--   * `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_123
import Definitions.Def_RPLib_FX_EtPBC_175

/-!
# Proper base change for the projective line, library file 183

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_Inj0d1`: S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
* `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_Inj0d1 =====
section

/-!
# S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem goodPt_fac [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0) :
    goodPt Λ g s j G α h ≫ (good Λ g s j G α).ι = j.2.left :=
  IsOpenImmersion.lift_fac _ _ _

theorem goodPt_w [UniversallyClosed g] (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (h : Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α = 0) :
    goodPt Λ g s j G α h ≫ ((Scheme.Etale.forget S).obj (opn j.1 (good Λ g s j G α))).hom =
      (CategoryTheory.Over.mk s.pt).hom :=
  (congrArg (fun φ => goodPt Λ g s j G α h ≫ φ) ((forget_obj_hom' (opn j.1 (good Λ g s j G α))).trans
    (opn_hom' j.1 (good Λ g s j G α)))).trans
  (((Category.assoc (goodPt Λ g s j G α h) (good Λ g s j G α).ι j.1.hom).symm.trans
    (congrArg (fun φ => φ ≫ j.1.hom) (goodPt_fac Λ g s j G α h))).trans
    ((nbhd_w (s := s) j).trans (Over.mk_hom s.pt).symm))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b3 =====
section

/-!
# S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`

`a' : D♭ ×_P Uz' ⟶ ιP^* DzO`, `a : D♭ ⟶ ιP^* Dz`, `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`, `c := σP`, with the four squares
`h₁ .. h₄` (all proved on underlying scheme maps through `toPull`), and **`mvTheta_Db`**:
`Λ[σP] ∘ (ιP^*MVZ-class of κ, r) = (locC D♭-class of a'^*κ, a ≫ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Mor

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)

/-- **MV-theta classes along `locC(D♭) ⟶ ιP^* MVZ`.** -/
theorem mvTheta_Db (Λ : Type) [CommRing Λ]
    {hsq₂ : (etPull (ιP gS s)).map
        (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a)))) ≫
      (etPull (ιP gS s)).map (wz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) =
      (etPull (ιP gS s)).map (p₂z K gS (zc c a) (chart_hclA c a) W (Qc gS c)) ≫
      (etPull (ιP gS s)).map
        (prW (Zz K gS (zc c a) (chart_hclA c a) W) (opEt (Uz K gS (zc c a) (chart_hclA c a))))}
    (hS₂ : (mvC Λ _ _ _ _ hsq₂).ShortExact) {R : (P1 K).Etale}
    (r : (etPull (ιP gS s)).obj (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) ⟶ R)
    (κ : H Λ (unitSh Λ ((etPull (ιP gS s)).obj (prd (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a))))).left) 1) :
    (Ext.mk₀ (freeMap Λ (σP gS s c a W (v' gS s c a W φ ht hP s') (v'_hom gS s c a W φ ht hP s')))).comp
      (hS₂.extClass.comp ((thetaM Λ ((etPull (ιP gS s)).map
        (prW (Dz K gS (zc c a) (chart_hclA c a) W (Qc gS c)) (opEt (Uz K gS (zc c a) (chart_hclA c a))))) 1 κ).comp
          (Ext.mk₀ (freeMap Λ r)) (add_zero 1)) (show 1 + 1 = 2 from rfl)) (zero_add 2) =
      (hSb gS s c a W φ ht hP s' Λ Uz' hUz').extClass.comp
        ((thetaM Λ (prW (Db gS s c a W φ ht hP s') (opEt Uz')) 1
          (resLE (aM' gS s c a W φ ht hP s' Uz' hUz').left 1 κ)).comp
            (Ext.mk₀ (freeMap Λ (aM gS s c a W φ ht hP s' ≫ r))) (add_zero 1)) (show 1 + 1 = 2 from rfl) :=
  mvTheta_map _ _ _ _ (h₁M gS s c a W φ ht hP s' Uz' hUz') (h₂M gS s c a W φ ht hP s' Uz' hUz')
    (h₃M gS s c a W φ ht hP s') (h₄M gS s c a W φ ht hP s' Uz' hUz') _ hS₂ r κ

end Mor

end RamanujanPetersson.EtPBC.EtMV

end

end

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

theorem pcD_s' : (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s')) (add_zero 2) =
    hS.extClass.comp ((thetaM Λ (prW (chEt c φ) (opEt Uz')) 1 (κD c a φ Uz' hN Λ hΛ hUz c')).comp
      (Ext.mk₀ (freeMap Λ s')) (add_zero 1)) (show 1 + 1 = 2 from rfl) := by
  have h := thetaM_res Λ (isoT c φ hUz).inv (toD1 c φ a) (resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c'))
  rw [isoT_inv_toD1] at h
  rw [pcD_eq, h, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

/-- **Shrinking the chart to `D♭`.** -/
theorem shrink_Db (κ : H Λ (unitSh Λ (prd (chEt c φ) (opEt Uz')).left) 1) :
    hS.extClass.comp ((thetaM Λ (prW (chEt c φ) (opEt Uz')) 1 κ).comp
      (Ext.mk₀ (freeMap Λ s')) (add_zero 1)) (show 1 + 1 = 2 from rfl) =
    (hSb gS s c a W φ ht hP s' Λ Uz' hUz').extClass.comp ((thetaM Λ (prW (Db gS s c a W φ ht hP s') (opEt Uz')) 1
      (resLE (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left 1 κ)).comp
        (Ext.mk₀ (freeMap Λ (opnι (chEt c φ) (Vb gS s c a W φ ht hP s') ≫ s'))) (add_zero 1))
      (show 1 + 1 = 2 from rfl) := by
  have h := mvTheta_map (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz'))
    (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (𝟙 (opEt Uz')) (𝟙 (etId (P1 K))) (prdMap_prW _ _)
    (hk₂ gS s c a W φ ht hP s' Uz') (toTop_ext _ _) (toTop_ext _ _) (hSb gS s c a W φ ht hP s' Λ Uz' hUz') hS s' κ
  rw [freeMap_id, Ext.mk₀_id_comp] at h
  exact h

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end


