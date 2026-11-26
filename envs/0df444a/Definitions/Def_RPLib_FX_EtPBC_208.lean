-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_208
-- name    : RPLib_FX_EtPBC_208
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:56:10.391225+00:00
-- url     : https://prove2.me/theorems/566e41ab-c91d-5682-b4a1-3fc56d833293
-- title:
--   Proper base change for the projective line, library file 208
-- statement:
--   File 208 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
--   * `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
--   * `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
--   * `S4.Def_RP_EtPBC_A_EGen`: S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_177
import Definitions.Def_RPLib_FX_EtPBC_204

/-!
# Proper base change for the projective line, library file 208

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
* `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
* `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
* `S4.Def_RP_EtPBC_A_EGen`: S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`
* `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_NbExt3 =====
section

/-!
# S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`

* `exists_affine_nbhd`: an affine noetherian neighbourhood of `s` (S locally noetherian);
* `exists_sec_vv`: a section `z` over some `Y_j` with `cval z ∘ ysj j = vv b` (induction over the finitely many values,
  each step `exists_clopen_nbhd` + `exists_indicator` + restriction);
* **`bcSurj_push_const`**: `BCSurj Λ (qV K gK) s 0 (π_* M_Y)` for `π : Y ⟶ P¹_S` finite.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {M : ModuleCat.{u} Λ}

/-- **Base change is surjective in degree `0` for `π_* M_Y`** (`π : Y ⟶ P¹_S` finite, `S` locally noetherian,
`s` a geometric point with `s ≫ g_K` an isomorphism). -/
theorem bcSurj_push_const [IsIso (s.pt ≫ gK)] [IsFinite π] [IsLocallyNoetherian S] :
    BCSurj Λ (qV K gK) s 0 ((push π Λ).obj (constSh Λ Y M)) := by
  intro β
  obtain ⟨j, z, hz⟩ := exists_sec_vv K gK s π (Ext.addEquiv₀ β)
  refine ⟨j, Ext.addEquiv₀.symm
    ((freeEquiv Λ ((etPull (qV K gK)).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z), ?_⟩
  exact (bc_zero_eq Λ (qV K gK) s j _ _).trans ((congrArg (fun φ => Ext.mk₀ (bcUnit Λ (qV K gK) s j ≫
    (pull (fibι (qV K gK) s) Λ).map φ)) (AddEquiv.apply_symm_apply _ _)).trans
    ((congrArg Ext.mk₀ (bc_eq_of_vv (qV K gK) s π (Ext.addEquiv₀ β) j z hz)).trans (Ext.mk₀_addEquiv₀_apply β)))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCc =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion

`Φ : U ⟶ P` finite, `ι : Ps ⟶ P` a closed immersion, `φs = pullback.snd Φ ι : U ×_P Ps ⟶ Ps`:
* `rC M Φ ι : Φ_* M_U ⟶ ι_* φs_* M_{U_s}` (restriction of sections to `U_s`);
* `eC M Φ ι : ι^* Φ_* M_U ⟶ φs_* M_{U_s}` its adjoint;
* **`isIso_eC`**: `eC` is an isomorphism (stalks via `rStk_bijective`, closed-immersion counit iso).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section BC

variable {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P)

/-- **Finite base change along a closed immersion, constant coefficients**: `eC` is an isomorphism. -/
theorem isIso_eC [IsFinite Φ] [IsClosedImmersion ι] : IsIso (eC M Φ ι) := by
  have hc : IsIso (pullAdj ι Λ).counit := isIso_closed_counit Λ ι
  rw [eC_eq]
  suffices IsIso ((pull ι Λ).map (rC M Φ ι)) from IsIso.comp_isIso
  rw [isIso_iff_stalk]
  intro z
  have hn := (pullStalkIso ι Λ (geomPtAt z)).hom.naturality (rC M Φ ι)
  have h2 := isIso_stalk_rC (M := M) Φ ι (geomPtAt z)
  have he : ((geomPtAt z).stalkF Λ).map ((pull ι Λ).map (rC M Φ ι)) =
      (pullStalkIso ι Λ (geomPtAt z)).hom.app _ ≫ (((geomPtAt z).map ι).stalkF Λ).map (rC M Φ ι) ≫
        (pullStalkIso ι Λ (geomPtAt z)).inv.app _ := by
    rw [← Category.assoc, ← hn]
    simp
  rw [he]
  infer_instance

end BC

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dA =====
section

/-!
# S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension

* `sesPb`: pulling the injective presentation `0 → A → I → I/A → 0` back along `x : X ⟶ I/A`;
* **`exists_ses_extClass`**: every `β ∈ Ext¹(X, A)` is the class of a short exact `0 → A → E → X → 0`;
* **`exists_bc_of_ses_kill`**: for `f : P' ⟶ P` etale with a closed lift `ι'` of the fibre inclusion, `Φ : U ⟶ P'`
  finite and a mono `m : f^* G ⟶ Φ_* M_U`, the class of an extension `0 → ι^* G →a E → Λ → 0` on `P_s` is a germ
  as soon as `(ι^* G ⟶ ι'^* f^* G ⟶ ι'^* Φ_* M_U ≅ φs_* M_{U_s})` extends along `a`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

universe w v₁ u₁

section Abstract

section Pb

end Pb

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.PushKill RamanujanPetersson.EtPBC.FBC

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Kill by an extension**: if the comparison map `ι^* G ⟶ φs_* M_{U_s}` extends along `a`, the extension
class of `0 → ι^* G → E → Λ → 0` is the base change of a germ. -/
theorem exists_bc_of_ses_kill (hQ : ∀ Q : EtSh Λ P, BCSurj Λ g s 0 Q) {P' U : Scheme.{u}} (f : P' ⟶ P)
    [Etale f] (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s) [IsClosedImmersion ι'] (Φ : U ⟶ P') [IsFinite Φ]
    {M : ModuleCat.{u} Λ} {G : EtSh Λ P} (m : (pull f Λ).obj G ⟶ (push Φ Λ).obj (constSh Λ U M)) [Mono m]
    {E : EtSh Λ (fib g s)} (a : (pull (fibι g s) Λ).obj G ⟶ E) (b : E ⟶ unitSh Λ (fib g s)) (w : a ≫ b = 0)
    (hS : (ShortComplex.mk a b w).ShortExact)
    (κ : E ⟶ (push (pullback.snd Φ ι') Λ).obj (constSh Λ (pullback Φ ι') M))
    (hκ : a ≫ κ = (liftIso g s f ι' hι).inv.app G ≫ (pull ι' Λ).map m ≫ eC M Φ ι') :
    ∃ (j : Nbhd s) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 1),
      Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 1 α =
        hS.extClass := by
  refine exists_bc_of_push_kill g s hQ f ι' hι m hS.extClass ?_
  have hi : IsIso (eC M Φ ι') := isIso_eC Φ ι'
  set y := (hS.extClass.comp (Ext.mk₀ ((liftIso g s f ι' hι).inv.app G)) (add_zero 1)).comp
    (Ext.mk₀ ((pull ι' Λ).map m)) (add_zero 1) with hy
  have h1 : y.comp (Ext.mk₀ (eC M Φ ι')) (add_zero 1) = 0 := by
    rw [hy, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀, ← hκ, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
    rw [show hS.extClass.comp (Ext.mk₀ a) (add_zero 1) = 0 from hS.extClass_comp, Ext.zero_comp]
  have h2 := congrArg (fun z => z.comp (Ext.mk₀ (inv (eC M Φ ι'))) (add_zero 1)) h1
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id, Ext.comp_mk₀_id,
    Ext.zero_comp] at h2
  exact h2

end Geo

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_EGen =====
section

/-!
# S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`

* **`genStep_of`**: on a noetherian `P` locally of finite type over a perfect field, if `BCSurj 0` holds for every
  `π_* M_Y` with `π` finite, then the generic step `GenStep` holds;
* **`genStep_qV`**: the generic step for `P¹_S ⟶ S` (`S` noetherian of finite type over a perfect field `K`, `s` a
  geometric point with `s ≫ g_K` an isomorphism);
* **`bcSurj_zero_qV`**: base change is surjective in degree `0` for every sheaf on `P¹_S`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **The generic step for `P¹_S ⟶ S`.** -/
theorem genStep_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] : GenStep Λ (qV K gK) s := by
  have : IsNoetherian (PV K gK) := {}
  exact genStep_of (qV K gK) s K p (qV K gK ≫ gK) fun π _ M => bcSurj_push_const K gK s π

/-- **`BCSurj 0` for every sheaf on `P¹_S`** (`S` noetherian of finite type over a perfect field). -/
theorem bcSurj_zero_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] (G : EtSh Λ (PV K gK)) : BCSurj Λ (qV K gK) s 0 G := by
  have : IsNoetherian (PV K gK) := {}
  exact bcSurj_zero_all (qV K gK) s (genStep_qV K p gK s) G

end RamanujanPetersson.EtPBC.GenGeo

end

end

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

/-- **The generic step for a predicate `C` holding on pushforwards of constant sheaves along finite maps.** -/
theorem genStepP_of (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (h : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] [NoetherianSpace P] [IsNoetherianRing Λ]
    [Finite Λ] (C : EtSh Λ P → Prop)
    (hBC : ∀ {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] (M : ModuleCat.{u} Λ) [Finite M],
      C ((push π Λ).obj (constSh Λ Y M))) : GenStepP Λ C := by
  classical
  intro Z hZ hne F hF _
  obtain ⟨J, hJ, W, hW, e, he⟩ := hF
  have : ∀ j, IsAffine (W j).left := hW
  obtain ⟨η, hηZ, V₀, hηV₀, hV₀⟩ := exists_generic_open Z hZ hne
  have hqc : ∀ V : P.Etale, IsAffine V.left → QuasiCompact V.hom := fun V _ => by
    have : CompactSpace V.left := inferInstance
    exact @quasiCompact_of_compactSpace _ _ V.hom this (inferInstanceAs (QuasiSeparatedSpace P))
  have : ∀ j, QuasiCompact (W j).hom := fun j => hqc _ (hW j)
  obtain ⟨T, t, τ, hτ, hgood, huniq⟩ := exists_good F hqc η W hW (gen e)
  have hfin : IsFinite (πn T (fpt η t)) := isFinite_πn T (fpt η t) K p h
  have hfib : ∀ j, Finite ((geomPtAt η).point.fiber.obj (W j)) := fun j => finite_fiber (W j) η
  have hsh : ∀ j, ∃ C : (geomPtAt η).point.fiber.obj (W j) → Set (Up (fpt η t) (W j)),
      (∀ b, IsClopen (C b)) ∧ (∀ u, ∃! b, u ∈ C b) ∧
      (∀ b, κp (fpt η t) (W j) (sx (fpt η t) (W j) (τ ⟨j, b⟩) default) ∈ C b) := fun j => by
    have := hfib j
    exact exists_sheets (W j) η t (fun b => τ ⟨j, b⟩) (fun b => hτ ⟨j, b⟩)
  choose C hCo hCp hCd using hsh
  have hfs : ∀ j, ∃ fj : (constSh Λ (Yn T (fpt η t)) (Mq F W (gen e) η)).obj.obj
      (op ((etPull (πn T (fpt η t))).obj (W j))), ∀ b (u : ((etPull (πn T (fpt η t))).obj (W j)).left),
      u ∈ C j b → cval fj u = mkv F W (gen e) η ⟨j, b⟩ := fun j => by
    have := hfib j
    exact exists_fsec (V := (etPull (πn T (fpt η t))).obj (W j)) (C j) (hCo j) (hCp j) _
  choose f hf using hfs
  let H : EtSh Λ P := (push (πn T (fpt η t)) Λ).obj (constSh Λ (Yn T (fpt η t)) (Mq F W (gen e) η))
  obtain ⟨φ, hφ⟩ := exists_desc e he H (fun j => f j) fun x l hl =>
    LinearMap.mem_ker.2 (ef_rel F W (gen e) η t τ hτ (fun j => f j) (fun q => hf q.1 q.2 _ (hCd q.1 q.2)) x l
      (LinearMap.mem_ker.1 hl))
  have hTo : IsOpen (Set.range T.hom) := by
    have : Etale T.hom := T.prop
    exact T.hom.isOpenMap.isOpen_range
  have : Finite (FibPts η W) := finite_fibPts η W
  have : Finite (FibPts η W →₀ Λ) := Finite.of_injective (fun f : FibPts η W →₀ Λ => (f : FibPts η W → Λ))
    DFunLike.coe_injective
  have : Finite (Mq F W (gen e) η) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨⟨Set.range T.hom ∩ V₀, hTo.inter V₀.isOpen⟩, H, φ, hBC _ _, ?_, ?_⟩
  · exact ⟨η, ⟨⟨fpt η t, fib_over η t⟩, hηV₀⟩, hηZ⟩
  · rintro x ⟨⟨⟨v, rfl⟩, hxV₀⟩, hxZ⟩
    have hsp : η ⤳ T.hom v := specializes_iff_mem_closure.2 (hV₀ ⟨hxV₀, hxZ⟩)
    have hξv := specializes_of_unique T η t huniq v hsp
    refine mono_stalk e he φ (T.hom v) fun l hl => ?_
    rw [show (fun j => (φ.hom.app (op (W j))).hom (gen e j)) = fun j => f j from funext hφ] at hl
    exact LinearMap.mem_ker.2 (eg_rel F W (gen e) η t τ hτ hgood (fun q => C q.1 q.2)
      (fun q => (hCo q.1 q.2).isClosed) (fun q => hCd q.1 q.2) f (fun q u hu => hf q.1 q.2 u hu) v hξv l
      (LinearMap.mem_ker.1 hl))

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gd =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes

* `graph_left_eq_of_fib`: sections with the same value at a geometric point have meeting graphs there;
* `mem_graph_of_card`: if disjoint graphs of sections `τ i : W ⟶ T` are at least as many as the points of every
  geometric fibre of `T` (finite), every point of `W ×_P T` lies on one of the graphs;
* `isZero_freeSh_of_isEmpty`, `ext_eq_zero_of_isZero`;
* **`isLoc_free_good`**: for `T` quasi-compact separated etale over `P` and `z = c (X = a)` a point where the fibre of
  `T` is as large as any fibre (a good point: constant degree near `z`), every one-point class at `z` with
  coefficients `Λ[T]` is in the subgroup generated by the point classes `PtCls` (the residual of `isLoc_free_decomp`
  is EMPTY).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

universe u w

section GoodGeo

end GoodGeo

section Zero

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] (a : k) {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

set_option backward.isDefEq.respectTransparency false in
include hN hΛ in
/-- The `clsD` part of `isLoc_free_good` (split for the kernel budget). -/
def isLoc_free_good_tail {T : P.Etale} [IsSeparated T.hom] [QuasiCompact T.hom] {ι : Type} [Fintype ι]
    (hcard : ∀ x : P, Nat.card ((geomPtAt x).point.fiber.obj T) ≤ Nat.card ι)
    {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [hφE : Etale (Spec.map φ ≫ c)] (hφ : φ.hom.Etale)
    [hded : IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
    {Uz : P.Opens} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
    (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
    (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact) (τ : ι → (chEt c φ ⟶ T))
    (hdisj : ∀ t t', t ≠ t' → Disjoint (Set.range (graph (τ t)).left) (Set.range (graph (τ t')).left))
    (Y₀ : H Λ ((res (toD1 c φ a).left Λ).obj ((res (chEt c φ).hom Λ).obj (freeSh Λ T))) 1) :
    clsD c φ a hUz hS (𝟙 _) Y₀ ∈ AddSubgroup.closure {x | PtCls Λ c hN hΛ T x} := by
  classical
  rw [← Iso.inv_hom_id (resFreeIso Λ (chEt c φ).hom T), clsD_comp]
  obtain ⟨R, g, hg, hR, hRa, YR, h1, -, h3⟩ := clsD_splitAll c φ a hUz hS
    (N := (etPull (chEt c φ).hom).obj T) (fun t => graph (τ t)) hdisj
    (resFreeIso Λ (chEt c φ).hom T).hom
    (Y₀.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map (resFreeIso Λ (chEt c φ).hom T).inv)) (add_zero 1))
    Finset.univ
  have hempty : IsEmpty R.left := ⟨fun r => by
    obtain ⟨b, hb⟩ := mem_graph_of_card τ hdisj (fun x => finite_fiber T x) hcard (g.left r)
    exact h1 r b (Finset.mem_univ b) hb⟩
  rw [clsD_eq_zero_of_isEmpty c a φ hUz hS hempty, sub_zero] at h3
  refine AddSubgroup.closure_mono ?_ h3
  rintro x ⟨i, -, Y', rfl⟩
  exact clsD_graph_mem c a hN hΛ φ hφ ht hP hz hUz hS (τ i) Y'

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end


