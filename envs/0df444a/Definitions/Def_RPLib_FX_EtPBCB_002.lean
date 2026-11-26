-- Prove2me | Definitions.Def_RPLib_FX_EtPBCB_002
-- name    : RPLib_FX_EtPBCB_002
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:04:45.550962+00:00
-- url     : https://prove2.me/theorems/4c05eda4-1c88-5518-a293-1107e6bfca44
-- title:
--   Proper base change for iterated projective-line bundles, library file 002
-- statement:
--   File 002 of the proper base change library for iterated projective-line bundles: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
--   * `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
--   * `S4.Def_RP_EtPBC_B_DLeray`: S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)
--   * `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
--   * `S4.Def_RP_EtPBC_B_MateB`: S4-EtPBC-B, C4 part 1b: the mate identity
--   * `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
--
--   **Formalization note.** One file of a library formalizing proper base change for iterated projective-line bundles: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the tower $X_0 = \mathbf P^1_S$, $X_{k+1} = \mathbf P^1_{X_k}$ with structure maps $f_k : X_k \to S$ (so $X_n = (\mathbf P^1)^{n+1}_S$) and a $K$-point $s$ of $S$, the stalk of $R^q f_{n*} F$ at $s$ is the étale cohomology $H^q(X_{n,s}, F|_{X_{n,s}})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. It builds on the proper base change library for the projective line (`RPLib_FX_EtPBC_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_212

/-!
# Proper base change for iterated projective-line bundles, library file 002

Declarations of the formalization of proper base change for the étale cohomology of the iterated
projective-line bundles (P¹)^(n+1)_S → S (geometric stalks of the higher direct images are the étale
cohomology of the geometric fibres), re-hosted declaration by declaration from the library modules
below, on top of the proper base change library for the projective line (RPLib_FX_EtPBC). Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_B_C1`: S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish
* `S4.Def_RP_EtPBC_B_NatZ`: S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test
* `S4.Def_RP_EtPBC_B_DLeray`: S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)
* `S4.Def_RP_EtPBC_B_Sec`: S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite
* `S4.Def_RP_EtPBC_B_MateB`: S4-EtPBC-B, C4 part 1b: the mate identity
* `S4.Def_RP_EtPBC_B_Tower`: S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_B_C1 =====
section

/-!
# S4-EtPBC-B, C1: higher direct images of `ι_* ι^* I` along the `P^1`-bundle vanish

For `h = qV K gY : PV K gY ⟶ Y` (`gY = g ≫ gS`), `f = h ≫ g`, a `K`-rational point `s` of `S`, the closed
fibre inclusion `ι : X_s ⟶ X` of `f` and an injective sheaf `I` on `X = PV K gY`:
* `fibMap`, `fibMap_ι`: if `t.pt ≫ g = a ≫ s.pt`, the fibre `X_t` of `h` maps to `X_s` over `X`;
* `pullNIso`: then `ι_t^* ι_* ι^* I ≅ ι_t^* I` (closed counit);
* `isZero_pull_push`: if `g t̄ ≠ s̄`, `ι_t^* ι_* G = 0` (stalks);
* **`rDer_N_isZero`**: `R^(n+1) h_* (ι_* ι^* I) = 0` (closed points of `Y` + `pbc_P1` + Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Fib

variable {Λ : Type u} [CommRing Λ]

theorem H_eq_zero_of_isZero {X : Scheme.{u}} {G : EtSh Λ X} (hG : IsZero G) (n : ℕ) (β : H Λ G n) :
    β = 0 := by
  rw [← Abelian.Ext.comp_mk₀_id β, hG.eq_of_src (𝟙 G) 0, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

section Map

end Map

end Fib

section C1

end C1

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_NatZ =====
section

/-!
# S4-EtPBC-B, C2a: naturality of degree-0 base change, and closed-point isomorphism test

* `sec0Ext_natural`, `stalkBC0_natural`, **`stalkEquiv0_natural`**: the degree-0 stalk base change equivalence
  `(g_* F)_s̄ ≃ H^0(P_s̄, ι^* F)` is natural in `F`;
* **`bijective_stalk_push`**: if `ι^* φ` is an isomorphism, `(g_* φ)_s̄` is bijective (given the degree-0 germ
  conditions); **`bijective_stalk_push_qV`** for `P^1_V ⟶ V` at a `K`-rational point;
* **`isIso_of_closed`**: on `X` locally of finite type over a field, a map of sheaves whose stalk maps at the closed
  points are bijective is an isomorphism (Jacobson).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.Z3

universe u

section Nat

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem sec0Ext_natural {F F' : EtSh Λ P} (φ : F ⟶ F') (V : S.Etale)
    (z : ((sheafToPresheaf _ _).obj ((push g Λ).obj F)).obj (op V)) :
    sec0Ext Λ g F' V ((((push g Λ).map φ).hom.app (op V)).hom z) =
      (sec0Ext Λ g F V z).comp (Ext.mk₀ φ) (add_zero 0) := by
  change Ext.mk₀ ((freeEquiv Λ ((etPull g).obj V) F').symm
      ((φ.hom.app (op ((etPull g).obj V))).hom z)) =
    (Ext.mk₀ ((freeEquiv Λ ((etPull g).obj V) F).symm z)).comp (Ext.mk₀ φ) (add_zero 0)
  rw [Ext.mk₀_comp_mk₀]
  congr 1
  rw [AddEquiv.symm_apply_eq, freeEquiv_comp]
  exact (congrArg (fun w => (φ.hom.app (op ((etPull g).obj V))).hom w)
    ((freeEquiv Λ ((etPull g).obj V) F).apply_symm_apply z)).symm

end Nat

section Closed

end Closed

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_DLeray =====
section

/-!
# S4-EtPBC-B, A1: the degenerate Leray argument (vanishing form)

Generic (`adj : L ⊣ R` between abelian categories, `L` preserving monomorphisms, `P` an injective resolution of
`N`, `R^(n+1) N = 0` for all `n`):
* `pushCx P = R(P)`, `pushCx_exactAt`: exact in degrees `≥ 1`;
* **`pushRes adj P hR`**: `R(P)` is an injective resolution of `R N`;
* **`ext_eq_zero_of_push`**: for `e : L A ≅ B`, `Ext^(n+1)(A, R N) = 0` implies `Ext^(n+1)(B, N) = 0`.
Sheaves: **`H_eq_zero_of_push`**: if `R^(p+1) h_* N = 0` for all `p` and `H^(n+1)(Y, h_* N) = 0`, then
`H^(n+1)(X, N) = 0`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.DLeray

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [HasInjectiveResolutions C]
  {L : D ⥤ C} {R : C ⥤ D} [R.Additive] (adj : L ⊣ R) [L.PreservesMonomorphisms]
  {N : C} (P : InjectiveResolution N)

/-- `R` applied to an injective resolution. -/
abbrev pushCx : CochainComplex D ℕ := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex

theorem pushCx_exactAt (hR : ∀ n : ℕ, IsZero ((R.rightDerived (n + 1)).obj N)) (n : ℕ) :
    (pushCx (R := R) P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hR n).of_iso (P.isoRightDerivedObj R (n + 1)).symm

omit [HasInjectiveResolutions C] in
theorem pushCx_d (i j : ℕ) : (pushCx (R := R) P).d i j = R.map (P.cocomplex.d i j) := rfl

/-- The augmentation `R N ⟶ R(P⁰)`. -/
def ι0 : R.obj N ⟶ (pushCx (R := R) P).X 0 := R.map (P.ι.f 0)

omit [HasInjectiveResolutions C] in
theorem ι0_d : ι0 (R := R) P ≫ (pushCx (R := R) P).d 0 1 = 0 :=
  (R.map_comp (P.ι.f 0) (P.cocomplex.d 0 1)).symm.trans
    ((congrArg R.map P.ι_f_zero_comp_complex_d).trans (R.map_zero _ _))

/-- **`R(P)` is an injective resolution of `R N`** when `R^(n+1) N = 0` for all `n`. -/
def pushRes (hR : ∀ n : ℕ, IsZero ((R.rightDerived (n + 1)).obj N)) : InjectiveResolution (R.obj N) where
  cocomplex := pushCx (R := R) P
  injective n := Injective.injective_of_adjoint adj (P.cocomplex.X n)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ι0 P, ι0_d P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · have : PreservesLimitsOfSize R := adj.rightAdjoint_preservesLimits
        have hfl : PreservesFiniteLimits R := inferInstance
        have key : ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map R).Exact ∧ Mono (R.map S.f) :=
          ((Functor.preservesFiniteLimits_tfae R).out 3 1).1 hfl
        have h := key (ShortComplex.mk _ _ P.ι_f_zero_comp_complex_d) ⟨P.exact₀, inferInstance⟩
        refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 h
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans ((CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (ι0 (R := R) P) (ι0_d P)).symm.trans (Category.comp_id _).symm))
          ((Category.id_comp _).trans (Category.comp_id _).symm)
      all_goals first | rfl | exact (pushCx (R := R) P).shape _ _ (by simp)
    · rw [quasiIsoAt_iff_exactAt]
      · exact pushCx_exactAt P hR _
      · apply CochainComplex.exactAt_succ_single_obj⟩

variable {A : D} {B : C} (e : L.obj A ≅ B) [HasExt.{w} C] [HasExt.{w} D]

include adj e in
/-- **Degenerate Leray, vanishing form.** -/
theorem ext_eq_zero_of_push (hR : ∀ n : ℕ, IsZero ((R.rightDerived (n + 1)).obj N)) (n : ℕ)
    (hA : ∀ α : Ext.{w} A (R.obj N) (n + 1), α = 0) (β : Ext.{w} B N (n + 1)) : β = 0 := by
  let P : InjectiveResolution N := injectiveResolution N
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective β (n + 2) rfl
  have hf' : adj.homEquiv _ _ (e.hom ≫ f) ≫ (pushRes adj P hR).cocomplex.d (n + 1) (n + 2) = 0 := by
    change adj.homEquiv _ _ (e.hom ≫ f) ≫ R.map (P.cocomplex.d (n + 1) (n + 2)) = 0
    rw [← adj.homEquiv_naturality_right, Category.assoc, hf, comp_zero, adj.homEquiv_unit, R.map_zero,
      comp_zero]
  obtain ⟨g', hg'⟩ := ((pushRes adj P hR).extMk_eq_zero_iff _ (n + 2) rfl hf' n rfl).1 (hA _)
  let g'' : A ⟶ R.obj (P.cocomplex.X n) := g'
  have hg'' : g'' ≫ R.map (P.cocomplex.d n (n + 1)) = adj.homEquiv _ _ (e.hom ≫ f) := hg'
  refine (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).2 ⟨e.inv ≫ (adj.homEquiv _ _).symm g'', ?_⟩
  rw [Category.assoc, ← adj.homEquiv_naturality_right_symm, hg'', Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

end RamanujanPetersson.EtPBC.DLeray

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_Sec =====
section

/-!
# S4-EtPBC-B, C4 part 2: the degree-0 base change unit of a composite

For `f = h ≫ g` and a neighbourhood `j` of `s`, `nbhdPsi : Λ[f⁻¹ V] ⟶ h^* Λ[g⁻¹ V]` and
**`bcUnit_psi`**: `bcUnit f ≫ ιX^*(nbhdPsi) = pullUnit h' ≫ h'^*(bcUnit g) ≫ sqQ` (an identity of global
sections over `X_s`: both are restrictions of `ιX^* h^*` of the tautological section, along two sections
`etId X_s ⟶ ιX⁻¹ h⁻¹ g⁻¹ V` that agree by `etPull3_hom_ext`).
Proofs about the components are term-mode chains: the objects `((etPull f).obj V).left` and
`pullback V.hom f` are only defeq, so `simp`/`rw` with `Category.assoc` do not see through them.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtPBC.EtMV

universe u

section Ext

variable {Xs X Y S : Scheme.{u}} (ιX : Xs ⟶ X) (h : X ⟶ Y) (g : Y ⟶ S) (U : S.Etale)

theorem etPull3_X (c : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj ((etPull g).obj U))) :
    c.left ≫ pullback.fst (((etPull h).obj ((etPull g).obj U)).hom) ιX ≫
      pullback.snd ((etPull g).obj U).hom h = ιX :=
  (whisker_eq c.left (pullback.condition (f := ((etPull h).obj ((etPull g).obj U)).hom) (g := ιX))).trans
    (((Category.assoc _ _ _).symm.trans (eq_whisker (MorphismProperty.Over.w c) ιX)).trans
      (Category.id_comp ιX))

/-- Sections `Xs ⟶ ιX⁻¹ h⁻¹ g⁻¹ U` are determined by their `U`-component. -/
theorem etPull3_hom_ext {a b : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj ((etPull g).obj U))}
    (hab : a.left ≫ pullback.fst (((etPull h).obj ((etPull g).obj U)).hom) ιX ≫
        pullback.fst ((etPull g).obj U).hom h ≫ pullback.fst U.hom g =
      b.left ≫ pullback.fst (((etPull h).obj ((etPull g).obj U)).hom) ιX ≫
        pullback.fst ((etPull g).obj U).hom h ≫ pullback.fst U.hom g) : a = b := by
  have hY : ∀ c : etId Xs ⟶ (etPull ιX).obj ((etPull h).obj ((etPull g).obj U)),
      c.left ≫ pullback.fst (((etPull h).obj ((etPull g).obj U)).hom) ιX ≫
        pullback.fst ((etPull g).obj U).hom h ≫ pullback.snd U.hom g = ιX ≫ h := fun c =>
    (whisker_eq _ (whisker_eq _ (pullback.condition (f := ((etPull g).obj U).hom) (g := h)))).trans
      (((whisker_eq _ (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans
        (eq_whisker (etPull3_X ιX h g U c) h))
  apply etPull_hom_ext ιX
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
      (hab.trans ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm)
  · exact (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (hY a)).trans
      (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (hY b)).symm
  · exact ((Category.assoc _ _ _).trans (etPull3_X ιX h g U a)).trans
      ((Category.assoc _ _ _).trans (etPull3_X ιX h g U b)).symm

end Ext

section Comp

theorem etComp_left_assoc {P : Scheme.{u}} {A B C : P.Etale} (a : A ⟶ B) (b : B ⟶ C) {W : Scheme.{u}}
    (k : C.left ⟶ W) : (a ≫ b).left ≫ k = a.left ≫ b.left ≫ k :=
  (eq_whisker (MorphismProperty.Comma.comp_left a b) k).trans (Category.assoc _ _ _)

theorem etPullCompIso_hom_fst_fst' {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (V : C.Etale) :
    ((etPullCompIso g f).hom.app V).left ≫ pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f =
      pullback.fst V.hom (g ≫ f) :=
  etPullCompIso_hom_fst_fst g f V

/-! Right-associated forms (the lib `_assoc` forms are left-associated). -/

theorem etPullCompIso_hom_fst_fst_r {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (V : C.Etale)
    {W : Scheme.{u}} (k : V.left ⟶ W) :
    ((etPullCompIso g f).hom.app V).left ≫ pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f ≫ k =
      pullback.fst V.hom (g ≫ f) ≫ k :=
  (whisker_eq ((etPullCompIso g f).hom.app V).left
    (Category.assoc (pullback.fst ((etPull f).obj V).hom g) (pullback.fst V.hom f) k).symm).trans
    ((Category.assoc ((etPullCompIso g f).hom.app V).left
      (pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f) k).symm.trans
      (eq_whisker (etPullCompIso_hom_fst_fst g f V) k))

theorem etPullCongr_left_fst_r {X Y : Scheme.{u}} {g g' : X ⟶ Y} (e : g = g') (T : Y.Etale)
    {W : Scheme.{u}} (k : T.left ⟶ W) :
    (etPullCongr e T).left ≫ pullback.fst T.hom g' ≫ k = pullback.fst T.hom g ≫ k :=
  (Category.assoc (etPullCongr e T).left (pullback.fst T.hom g') k).symm.trans
    (eq_whisker (etPullCongr_left_fst e T) k)

theorem etIdPull_hom_left_fst_r {X Y : Scheme.{u}} (g : X ⟶ Y) {W : Scheme.{u}} (k : Y ⟶ W) :
    (etIdPull g).hom.left ≫ pullback.fst (etId Y).hom g ≫ k = g ≫ k :=
  (Category.assoc (etIdPull g).hom.left (pullback.fst (etId Y).hom g) k).symm.trans
    (eq_whisker (etIdPull_hom_left_fst g) k)

end Comp

section SqN

variable {Λ : Type u} [CommRing Λ] {X Y Xs Ys : Scheme.{u}} (ιX : Xs ⟶ X) (ιY : Ys ⟶ Y) (h : X ⟶ Y)
  (h' : Xs ⟶ Ys) (w : h' ≫ ιY = ιX ≫ h)

/-- `sqQ.hom.app F`, typed with nested pullbacks (`pullCompInv ≫ pullCongr ≫ pullCompHom`). -/
def sqN (F : EtSh Λ Y) : (pull h' Λ).obj ((pull ιY Λ).obj F) ⟶ (pull ιX Λ).obj ((pull h Λ).obj F) :=
  pullCompInv Λ h' ιY F ≫ (pullCongr Λ w).hom.app F ≫ pullCompHom Λ ιX h F

/-- `sqN` on a restricted double pullback section. -/
theorem sqN_pbSec {F : EtSh Λ Y} {V : Y.Etale} {Z : Xs.Etale}
    (a : op ((etPull h').obj ((etPull ιY).obj V)) ⟶ op Z) (x : F.obj.obj (op V)) :
    ((sqN ιX ιY h h' w F).hom.app (op Z)).hom
        ((((pull h' Λ).obj ((pull ιY Λ).obj F)).obj.map a).hom (pbSec h' (pbSec ιY x))) =
      ((((pull ιX Λ).obj ((pull h Λ).obj F)).obj.map (((etPullCompIso ιX h).hom.app V).op ≫
        (etPullCongr w V).op ≫ ((etPullCompIso h' ιY).inv.app V).op ≫ a)).hom (pbSec ιX (pbSec h x))) :=
  appN3 (Λ := Λ) _ _ _ (pullCompInv_pbSecO h' ιY a x) (pullCongr_pbSecO w _ x) (pullCompHom_pbSecO ιX h _ x)

end SqN

section Psi

variable {Λ : Type u} [CommRing Λ]

theorem unit_pbSec {Z T : Scheme.{u}} (f : Z ⟶ T) (F : EtSh Λ T) (V : T.Etale) (x : F.obj.obj (op V)) :
    (((pullAdj f Λ).unit.app F).hom.app (op V)).hom x = pbSec f x := rfl

theorem mapMapApply {Z : Scheme.{u}} {F : EtSh Λ Z} {A B C : Z.Etale} (a : A ⟶ B) (b : B ⟶ C)
    (x : F.obj.obj (op C)) :
    (F.obj.map a.op).hom ((F.obj.map b.op).hom x) = (F.obj.map (a ≫ b).op).hom x := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

end Psi

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_B_MateB =====
section

/-!
# S4-EtPBC-B, C4 part 1b: the mate identity

Kernel note: `sqQ.hom.app` must only ever be applied to one spelling of an object (`(push h).obj
((push ιX).obj M)` versus `(push ιX ⋙ push h).obj M` makes the kernel unfold `pullCompIso`), so the
components of `pushCompIso` and of the unit are used through the nested-typed `pc` and `unitN`.
* `sq_counit`: `h'^* ιY^*(sqP) ≫ h'^*(ε_{ιY}) ≫ ε_{h'} = sqQ ≫ ιX^*(ε_h) ≫ ε_{ιX}`;
* `vMapG G : ιY^* h_* G ⟶ h'_* ιX^* G` and **`mateG`**: `h'^*(vMapG G) ≫ ε_{h'} = sqQ ≫ ιX^*(ε_h G)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Mate

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

/-- The component of `pushCompIso` with the nested source `b_* a_* M`. -/
def pc {W X Y : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (M : EtSh Λ W) :
    (push b Λ).obj ((push a Λ).obj M) ≅ (push (a ≫ b) Λ).obj M :=
  (pushCompIso Λ a b).app M

/-- The unit of `ι^* ⊣ ι_*` with the nested target `ι_* ι^* G`. -/
def unitN {Z X : Scheme.{u}} (ι : Z ⟶ X) (G : EtSh Λ X) : G ⟶ (push ι Λ).obj ((pull ι Λ).obj G) :=
  (pullAdj ι Λ).unit.app G

theorem unitN_triangle {Z X : Scheme.{u}} (ι : Z ⟶ X) (G : EtSh Λ X) :
    (pull ι Λ).map (unitN ι G) ≫ (pullAdj ι Λ).counit.app ((pull ι Λ).obj G) = 𝟙 _ :=
  (pullAdj ι Λ).left_triangle_components G

section Sq

end Sq

end RamanujanPetersson.EtPBC.Mate

end

end

-- ===== S4.Def_RP_EtPBC_B_Tower =====
section

/-!
# S4-EtPBC-B, C5/C6: proper base change for the iterated relative projective line

* `PBCGood Λ g s`: `BCSurj 0` for every sheaf plus fibre vanishing `FibVan`; it gives proper base change
  in all degrees for `g` universally closed (`pbc_of_good`);
* `good_qV`: `P^1_S ⟶ S` (`bcSurj_zero_qV` + `pbc_P1`);
* `good_comp`: `PBCGood g ⟹ PBCGood (P^1_Y ⟶ Y ⟶ S)` for `g` proper (`bcSurj_comp` + `fibVan_comp`);
* `towerP K gS n : Σ Y, Y ⟶ S` is `(P^1)^{n+1}_S` as an iterated `P^1`-bundle; **`pbc_towerP`**: proper
  base change `(R^q f_* F)_s ≃+ H^q(X_s, F|X_s)` for its structure map `f`, at `K`-rational `s`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

/-- `P^1_V` is Noetherian over a Noetherian `V`. -/
instance isNoetherian_PV (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K))
    [IsNoetherian V] : IsNoetherian (PV K gV) :=
  { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

section Good

end Good

section Step

end Step

section Tower

variable (K : Type) [Field K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))

/-- `(P^1)^{n+1}_S` as an iterated `P^1`-bundle over `S`, with its structure map. -/
def towerP : ℕ → Σ Y : Scheme.{0}, (Y ⟶ S)
  | 0 => ⟨PV K gS, qV K gS⟩
  | n + 1 => ⟨PV K ((towerP n).2 ≫ gS), qV K ((towerP n).2 ≫ gS) ≫ (towerP n).2⟩

theorem towerP_zero : towerP K gS 0 = ⟨PV K gS, qV K gS⟩ := rfl

theorem towerP_succ (n : ℕ) : towerP K gS (n + 1) =
    ⟨PV K ((towerP K gS n).2 ≫ gS), qV K ((towerP K gS n).2 ≫ gS) ≫ (towerP K gS n).2⟩ := rfl

instance isProper_towerP (n : ℕ) : IsProper (towerP K gS n).2 := by
  induction n with
  | zero => exact (inferInstance : IsProper (qV K gS))
  | succ n ih => exact (inferInstance : IsProper (qV K ((towerP K gS n).2 ≫ gS) ≫ (towerP K gS n).2))

instance isNoetherian_towerP [IsNoetherian S] (n : ℕ) : IsNoetherian (towerP K gS n).1 := by
  induction n with
  | zero => exact (inferInstance : IsNoetherian (PV K gS))
  | succ n ih => exact (inferInstance : IsNoetherian (PV K ((towerP K gS n).2 ≫ gS)))

end Tower

section Main

end Main

end RamanujanPetersson.EtPBC

end

end


