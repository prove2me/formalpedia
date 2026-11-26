-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_215
-- name    : RPLib_FX_EtPBC_215
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:42:14.547722+00:00
-- url     : https://prove2.me/theorems/631e3b34-5298-5600-8761-e4f8b4778285
-- title:
--   Proper base change for the projective line, library file 215
-- statement:
--   File 215 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
--   * `S4.Def_RP_EtPBC_A_PBCStk`: S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions
--   * `S4.Def_RP_EtPBC_A_O2Gen2`: S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_176
import Definitions.Def_RPLib_FX_EtPBC_212
import Definitions.Def_RPLib_FX_EtPBC_213
import Definitions.Def_RPLib_FX_EtPBC_214

/-!
# Proper base change for the projective line, library file 215

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
* `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
* `S4.Def_RP_EtPBC_A_PBCStk`: S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions
* `S4.Def_RP_EtPBC_A_O2Gen2`: S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_EGenP =====
section

/-!
# S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`

* **`genStepP_of`**: the generic step `GenStepP Λ C` for any predicate `C` that holds for every `π_* M_Y` with `π`
  finite and `M` finite, `Λ` finite (same proof as `genStep_of`, which is the case `C = BCSurj 0`);
* **`bcInj_one_qV`**: base change is injective on germs in degree `1` for every sheaf on `P¹_S` (δ-lemma from degree
  `0`: `bcInj_zero`, `bcSurj_zero_qV`);
* **`bcSurj_succ_fgt_qV`**: if `BCSurj (q+1)` holds for every `π_* M_Y` (`π` finite, `M` finite; `Λ` finite),
  `BCInj (q+1)` and `BCSurj q`
  for every sheaf, then `BCSurj (q+1)` holds for every `FGT` sheaf on `P¹_S`; **`bcSurj_one_fgt_qV`** (`q = 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **`BCSurj 1` for every `FGT` sheaf on `P¹_S`** from `BCSurj 1` for every `π_* M_Y` (`π` finite). -/
theorem bcSurj_one_fgt_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] [Finite Λ]
    (hC : ∀ {Y : Scheme.{u}} (π : Y ⟶ PV K gK) [IsFinite π] (M : ModuleCat.{u} Λ) [Finite M],
      BCSurj Λ (qV K gK) s 1 ((push π Λ).obj (constSh Λ Y M)))
    (F : EtSh Λ (PV K gK)) (hF : FGT Λ F) : BCSurj Λ (qV K gK) s 1 F :=
  bcSurj_succ_fgt_qV K p gK s 0 (bcInj_one_qV K p gK s) (bcSurj_zero_qV K p gK s) hC F hF

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_T2I =====
section

/-!
# S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`

* **`LiftT g s π`** (the remaining input, pure geometry): every finite etale surjective `T ⟶ Y_s` is dominated, over
  `Y_s`, by the fibre `U_s` of a finite `U ⟶ P'` over an etale neighbourhood `P' ⟶ P` of the fibre, with `U`
  covering `P' ×_P Y`.
* **`hypT_of_liftT`**: `T1` turns `LiftT` into `T3d.HypT` (given compactness of `Y_s` and affineness of etale maps
  from affine schemes to `Y_s`); `hypT_of_liftT'` discharges both for `g` separated, `fib g s` compact, `π` finite.
* **`bcSurj_one_push_of_liftT`**: degree-one base change for `π_* N_Y` from degree zero and `LiftT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree-one base change for `π_* N_Y`** from degree zero and the lifting input `LiftT`. -/
theorem bcSurj_one_push_of_liftT [IsClosedImmersion (fibι g s)] [IsSeparated g] [CompactSpace (fib g s)]
    (hQ : ∀ Q : EtSh Λ P, BCSurj Λ g s 0 Q) {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π]
    (N : ModuleCat.{u} Λ) [Finite N] (hL : LiftT g s π) :
    BCSurj Λ g s 1 ((push π Λ).obj (constSh Λ Y N)) :=
  T3d.bcSurj_one_push_of_hypT g s hQ π N (hypT_of_liftT' g s π N hL)

end RamanujanPetersson.EtPBC.T2

end

end

-- ===== S4.Def_RP_EtPBC_A_PBCStk =====
section

/-!
# S4-EtPBC-A, L1g: proper base change on stalks from the germ conditions

For `g : P ⟶ S` and a geometric point `s` of `S` (fibre `ι : P_s ⟶ P`):
* `pbcEquivSucc`: `(R^(p+1) g_* F)_s ≃+ H^(p+1)(P_s, ι^* F)` (from `stalkRDIso`, `germExt`, `stalkEquiv`);
* `pbcEquivZero`: `(R^0 g_* F)_s ≃+ H^0(P_s, ι^* F)` (from `rightDerivedZeroIsoSelf`, `freeEquiv`, `Ext.addEquiv₀`);
both given that base change is injective and surjective on germs in that degree for `F`.
**`pbc_of_germs`**: if base change is injective on germs in degree `0` and surjective on germs in every degree, for all
sheaves, then `(R^q g_* F)_s ≃+ H^q(P_s, ι^* F)` for all `q` and `F` (δ-lemma `Delta.injAt_all`).
(`pbcEquivZero` and `pbc_of_germs` are in `PBCStkb`, split off for the file time limit.)
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem sec0Ext_map (F : EtSh Λ P) : GermNat Λ g F 0 ((sheafToPresheaf _ _).obj ((push g Λ).obj F)) (sec0Ext Λ g F) := by
  intro V' V a z
  change Ext.mk₀ ((freeEquiv Λ ((etPull g).obj V') F).symm (F.val.map ((etPull g).map a).op z)) =
    (Ext.mk₀ (freeMap Λ ((etPull g).map a))).comp (Ext.mk₀ ((freeEquiv Λ ((etPull g).obj V) F).symm z)) (zero_add 0)
  rw [Ext.mk₀_comp_mk₀]
  congr 1
  apply (freeEquiv Λ ((etPull g).obj V') F).injective
  rw [freeEquiv_freeMap, AddEquiv.apply_symm_apply]
  exact (congrArg (fun y => F.val.map ((etPull g).map a).op y)
    (AddEquiv.apply_symm_apply (freeEquiv Λ ((etPull g).obj V) F) z)).symm

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen2 =====
section

/-!
# S4-EtPBC-A, O2 Gen2: one-point classes on `P¹` are sums of point classes

* `genT Λ hN hΛ T`: the subgroup generated by point classes `PtCls Λ c hN hΛ T` over all charts `c : A¹ ⟶ P¹`;
* `comp_mem_genT`: `genT` is stable under `x ↦ x ∘ Λ[r]`;
* `good_mem_genT`: an `IsLoc` class at a point of generic degree lies in `genT` (`isLoc_free_good`);
* `isLoc_comp_mem`: for `R` affine, every `IsLoc` class `β'` of `Λ[R]` has `β' ∘ Λ[r] ∈ genT` (`pp_isLoc` over a
  moved chart `chartM c₀` missing a generic-degree point);
* `isLoc_mem_genT`: every `IsLoc` class of `Λ[T]` lies in `genT` (`isLoc_free_res`);
* **`gen_free`**: with `N = l ^ m`, every class in `Ext² (Λ, Λ[T])` lies in `genT` (`mem_locSpan_P1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section Gen

variable {k : Type} [Field k] [IsAlgClosed k] (Λ : Type) [CommRing Λ] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)
  (hΛ : ∀ x : Λ, N • x = 0)

theorem good_mem_genT (R : (P1 k).Etale) [IsSeparated R.hom] [QuasiCompact R.hom] (x : P1 k)
    (hx : Nat.card ((geomPtAt x).point.fiber.obj R) = Nat.card ((geomPtAt (P1.genPt k)).point.fiber.obj R))
    (γ : Ext.{0} (freeSh Λ (etId (P1 k))) (freeSh Λ R) 2) (hγ : IsLoc Λ (freeSh Λ R) x γ) :
    γ ∈ genT Λ hN hΛ R := by
  obtain ⟨b, hb⟩ := exists_A1pt_of_mem_range (p1Chart k x) x (isClosed_of_isLoc hγ) ⟨_, p1Chart_p1Pt k x⟩
  have hγ' : IsLoc Λ (freeSh Λ R) (p1Chart k x (A1pt k b)) γ := by rw [hb]; exact hγ
  have hle : ∀ y : P1 k, Nat.card ((geomPtAt y).point.fiber.obj R) ≤
      Nat.card ((geomPtAt (p1Chart k x (A1pt k b))).point.fiber.obj R) := fun y => by
    rw [hb]; exact (card_le_genPt k R y).trans hx.ge
  refine (AddSubgroup.closure_le _).2 ?_ (isLoc_free_good (p1Chart k x) b hN hΛ (chart_hGal _ b) hle hγ')
  intro y hy
  exact mem_genT_of_ptCls Λ hN hΛ (p1Chart k x) hy

end Gen

section Free

end Free

end RamanujanPetersson.EtPBC.EtKum

end

end


