-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_112
-- name    : RPLib_FX_EtPBC_112
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:51:53.399897+00:00
-- url     : https://prove2.me/theorems/1f0b3f00-a9dd-4d58-8d80-0aa1ec8dd831
-- title:
--   Proper base change for the projective line, library file 112
-- statement:
--   File 112 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
--   * `S4.Def_RP_EtPBC_A_O2T4a00`: S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_083
import Definitions.Def_RPLib_FX_EtPBC_084
import Definitions.Def_RPLib_FX_EtPBC_099
import Definitions.Def_RPLib_FX_EtPBC_104

/-!
# Proper base change for the projective line, library file 112

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
* `S4.Def_RP_EtPBC_A_O2T4a00`: S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Th1a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality

Fix `D₀ R : P.Etale` with `W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`.
For `τ : T ⟶ D₀` (any `T : P.Etale` over `D₀`):
* **`theta Λ D₀ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`** (extension by zero to `D₀`, Shapiro for
  `W₀ ⟶ D₀`, pullback of free sheaves, `T ×_{D₀} W₀ ≅ T ×_P R`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm R m) (θ_{τ₂} x)` (`wm R m : T₁ ×_P R ⟶ T₂ ×_P R`);
* `extFreeV_natural` (naturality of `extFreeV` in `V`), `shapExt_symm_natural`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section ExtV

end ExtV

section ShapNat

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom]
  (n : ℕ) (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n)

/-- Naturality of `shapExt⁻¹` in the source. -/
theorem shapExt_symm_natural {A₀ A : EtSh Λ P} (c : A₀ ⟶ A) {k : ℕ} (z : Ext.{u} A (freeSh Λ W) k) :
    (shapExt Λ W n hn A₀ k).symm ((Ext.mk₀ c).comp z (zero_add k)) =
      (Ext.mk₀ ((pull W.hom Λ).map c)).comp ((shapExt Λ W n hn A k).symm z) (zero_add k) := by
  apply (shapExt Λ W n hn A₀ k).injective
  rw [AddEquiv.apply_symm_apply, shapExt_natural, AddEquiv.apply_symm_apply]

end ShapNat

section Theta

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4a00 =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4a00): section class map `thetaM` and `thetaM_eq` (split from O2T4a0 for the 150 user-s cap)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

/-- Unfolding equation for `thetaM`. KERNEL COST RULE (s102): rewrite with this lemma, never with `thetaM` itself (the
auto-generated equation carries the def's abstracted instance proofs, which are slow to compare with fresh ones). -/
theorem thetaM_eq {W T : P.Etale} (m : W ⟶ T) (n : ℕ) (κ : H Λ (unitSh Λ W.left) n) :
    thetaM Λ m n κ = (extFree Λ W (freeSh Λ T) n).symm (κ.comp (Ext.mk₀ (secMap Λ m)) (add_zero n)) :=
  rfl

end Theta

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4d =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Pc

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

include hN hΛ hUz hS in
/-- **The point class with coefficients `Λ[D]`**, `D = Spec B`. -/
def pcD (c' : Λ) : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ (chEt c φ)) 2 :=
  (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)).comp
    (thetaM Λ (toD1 c φ a) 1 (resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c'))) (show 1 + 1 = 2 from rfl)

end Pc

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

/-- **The Kummer classes agree on `D♭ ×_P Uz'`.** -/
theorem hκ : resLE (aM' gS s c a W φ ht hP s' Uz' hUz').left 1
    (pullH Λ (fW (ιP gS s) (DzO gS c a W)) 1 (κZ gS c a W hN Λ hΛ c')) =
      resLE (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left 1
        (κD c a φ Uz' hN Λ hΛ hUz c') := by
  have e1 := (resLE_eq_pullH (Λ := Λ) (aM' gS s c a W φ ht hP s' Uz' hUz').left
    (pullH Λ (fW (ιP gS s) (DzO gS c a W)) 1 (κZ gS c a W hN Λ hΛ c'))).trans
    ((congrArg (pullH Λ (aM' gS s c a W φ ht hP s' Uz' hUz').left 1)
      (pullH_comp (fW (ιP gS s) (DzO gS c a W)) (fA gS c a W) (xiA a hN Λ hΛ c')).symm).trans
      (pullH_comp _ _ _).symm)
  have e2 := (resLE_eq_pullH (Λ := Λ) (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left
    (κD c a φ Uz' hN Λ hΛ hUz c')).trans ((congrArg (pullH Λ
      (prdMap (opnι (chEt c φ) (Vb gS s c a W φ ht hP s')) (opEt Uz')).left 1)
      ((resLE_eq_pullH (Λ := Λ) (isoT c φ hUz).inv.left _).trans ((congrArg (pullH Λ (isoT c φ hUz).inv.left 1)
        (resLE_eq_pullH (Λ := Λ) (toWa c a φ).left (xiA a hN Λ hΛ c'))).trans (pullH_comp _ _ _).symm))).trans
      (pullH_comp _ _ _).symm)
  exact e1.trans ((congrArg (fun g => pullH Λ g 1 (xiA a hN Λ hΛ c'))
    (hmapA gS s c a W φ ht hP s' Uz' hUz' hUz)).trans e2.symm)

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

theorem hκ_E {W' : (PV K gS).Etale} (κ : H Λ (unitSh Λ W'.left) 1) :
    resLE (isoE gS s W').left 1 (pullH Λ (fW (fibι (qV K gS) s) W') 1 κ) =
      pullH Λ (fW (fibToP1 K gS s) ((etPull (ιP gS s)).obj W')) 1 (pullH Λ (fW (ιP gS s) W') 1 κ) := by
  rw [resLE_eq_pullH, ← pullH_comp, ← pullH_comp, isoE_left_fW]

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end


