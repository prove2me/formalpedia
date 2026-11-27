-- Prove2me | Definitions.Def_RPLib_FX_EtPBCC3_004
-- name    : RPLib_FX_EtPBCC3_004
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-27T06:48:54.949858+00:00
-- url     : https://prove2.me/theorems/32b94cff-16ea-592e-967a-588924b857c7
-- title:
--   Compactly supported étale cohomology of affine space with Tate twists, library file 004
-- statement:
--   File 004 of the library for compactly supported étale cohomology of affine space with Tate twists: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
--   * `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
--   * `S4.Def_RP_EtLeray_Bnd`: S4-EtLeray, part 9: boundary vanishing for compact supports
--   * `S4.Def_RP_EtLeray_RelA`: S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`
--   * `S4.Def_RP_EtLin_Gen`: S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)
--   * `S4.Def_RP_EtLin_ExtL`: S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps
--
--   **Formalization note.** One file of a library formalizing the étale cohomology with compact supports of affine space over an algebraically closed field $K$ with Tate-twisted coefficients: for $\Lambda$ a finite ring with $\ell^m \Lambda = 0$ ($\ell$ invertible in $K$) and $\Lambda(k)$ the constant sheaf $(\Lambda \otimes \mu_{\ell^m})^{\otimes k}$, $H^q_c(\mathbb{A}^{n+1}_K, \Lambda(k)) = 0$ for $q \ne 2n+2$ and $H^{2n+2}_c(\mathbb{A}^{n+1}_K, \Lambda(n+1)) \cong \Lambda$ $\Lambda$-linearly, via $R^q \mathrm{pr}_!$ of the relative affine line and induction on the dimension. It builds on the proper base change libraries (`RPLib_FX_EtPBC_*`, `RPLib_FX_EtPBCB_*`, `RPLib_FX_EtPBCC1_*`, `RPLib_FX_EtPBCC2_*`). The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XVII (P. Deligne, cohomologie à supports propres) and Exposé XVIII, 2.9 (P. Deligne, morphisme trace), Lecture Notes in Math. 305, Springer (1973); P. Deligne, SGA 4 1/2, [Arcata], Lecture Notes in Math. 569 (1977); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI

import Mathlib
import Definitions.Def_RPLib_FX_EtPBCB_005
import Definitions.Def_RPLib_FX_EtPBCC3_001

/-!
# Compactly supported étale cohomology of affine space with Tate twists, library file 004

Declarations of the formalization of compactly supported étale cohomology of affine space over an
algebraically closed field with Tate-twisted coefficients: H^q_c(A^(n+1), Λ(k)) = 0 for q ≠ 2n+2 and
H^(2n+2)_c(A^(n+1), Λ(n+1)) ≃ Λ, Λ-linearly, re-hosted declaration by declaration from the library
modules below, on top of the proper base change libraries RPLib_FX_EtPBC, RPLib_FX_EtPBCB,
RPLib_FX_EtPBCC1 and RPLib_FX_EtPBCC2. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtLeray_Shift`: S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)
* `S4.Def_RP_EtLeray_BCo`: S4-EtLeray, part 10: base change along arbitrary pullback squares
* `S4.Def_RP_EtLeray_Bnd`: S4-EtLeray, part 9: boundary vanishing for compact supports
* `S4.Def_RP_EtLeray_RelA`: S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`
* `S4.Def_RP_EtLin_Gen`: S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)
* `S4.Def_RP_EtLin_ExtL`: S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtLeray_Shift =====
section

/-!
# S4-EtLeray, part 2: shifting an injective resolution (dimension shift for `R^q`)

For an injective resolution `P` of `N` put `Qc P := coker(N → P⁰)`. Then `P^(•+1)` with the induced
`Qc P ↪ P¹` is an injective resolution `shRes P` of `Qc P`, and for any additive `R`
* **`dsIso P R q`**: `R^(q+1)(Qc P) ≅ R^(q+2) N`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : C} (P : InjectiveResolution N)

@[reassoc (attr := simp)]
theorem π_dQ : cokernel.π (P.ι.f 0) ≫ dQ P = P.cocomplex.d 0 1 := cokernel.π_desc _ _ _

theorem dQ_d12 : dQ P ≫ P.cocomplex.d 1 2 = 0 := by
  rw [← cancel_epi (cokernel.π (P.ι.f 0)), π_dQ_assoc, HomologicalComplex.d_comp_d, comp_zero]

theorem dQ_d : dQ P ≫ (shCx P).d 0 1 = 0 :=
  (congrArg (fun g => dQ P ≫ g) (shCx_d01 P)).trans (dQ_d12 P)

/-- `Qc P → P¹ → P²` is exact. -/
theorem shExact₀ : (ShortComplex.mk (dQ P) (P.cocomplex.d 1 2) (dQ_d12 P)).Exact := by
  have h : (ShortComplex.mk (P.cocomplex.d 0 1) (P.cocomplex.d 1 2)
      (P.cocomplex.d_comp_d 0 1 2)).Exact := P.exact_succ 0
  let φ : ShortComplex.mk (P.cocomplex.d 0 1) (P.cocomplex.d 1 2) (P.cocomplex.d_comp_d 0 1 2) ⟶
      ShortComplex.mk (dQ P) (P.cocomplex.d 1 2) (dQ_d12 P) :=
    { τ₁ := cokernel.π (P.ι.f 0)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (π_dQ P).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := (inferInstance : Epi (cokernel.π (P.ι.f 0)))
  have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (P.cocomplex.X 1)))
  have : Mono φ.τ₃ := (inferInstance : Mono (𝟙 (P.cocomplex.X 2)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h

set_option backward.isDefEq.respectTransparency false in
theorem ι_f0 : ((CochainComplex.fromSingle₀Equiv (shCx P) (Qc P)).symm ⟨dQ P, dQ_d P⟩).f 0 = dQ P :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The shifted injective resolution** of `Qc P`. -/
def shRes : InjectiveResolution (Qc P) where
  cocomplex := shCx P
  injective q := P.injective (q + 1)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨dQ P, dQ_d P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨shExact₀ P, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans ((ι_f0 P).symm.trans (Category.comp_id _).symm))
          (by simp [shCx_d01])
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt]
      · exact shCx_exactAt_succ P _
      · apply CochainComplex.exactAt_succ_single_obj⟩

theorem shRes_cocomplex : (shRes P).cocomplex = shCx P := rfl

variable [HasInjectiveResolutions C] {D : Type u'} [Category.{v'} D] [Abelian D] (R : C ⥤ D) [R.Additive]

/-- The short complexes computing `R^(q+1)(Qc P)` and `R^(q+2) N` agree. -/
def scIso (q : ℕ) :
    ((R.mapHomologicalComplex _).obj (shCx P)).sc' q (q + 1) (q + 2) ≅
      ((R.mapHomologicalComplex _).obj P.cocomplex).sc' (q + 1) (q + 2) (q + 3) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [shCx_d] <;> exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp [shCx_d'] <;> exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Dimension shift**: `R^(q+1)(Qc P) ≅ R^(q+2) N`. -/
def dsIso (q : ℕ) : (R.rightDerived (q + 1)).obj (Qc P) ≅ (R.rightDerived (q + 2)).obj N :=
  (shRes P).isoRightDerivedObj R (q + 1) ≪≫
    ((R.mapHomologicalComplex _).obj (shCx P)).homologyIsoSc' q (q + 1) (q + 2) (by simp)
      (by simp only [CochainComplex.next]; rfl) ≪≫
    ShortComplex.homologyMapIso (scIso P R q) ≪≫
    (((R.mapHomologicalComplex _).obj P.cocomplex).homologyIsoSc' (q + 1) (q + 2) (q + 3) (by simp)
      (by simp only [CochainComplex.next]; rfl)).symm ≪≫
    (P.isoRightDerivedObj R (q + 2)).symm

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_BCo =====
section

/-!
# S4-EtLeray, part 10: base change along arbitrary pullback squares

For a pullback square `IsPullback a b f g` (`a ≫ f = b ≫ g`):
* **`pullPushSq`** (`f` a closed immersion): `g^* f_* M ≅ b_* a^* M`;
* **`pullLshSq`** (`f` étale): `g^* f_! F ≅ b_! a^* F`;
* **`pullRDerSq`** (`g` étale): `g^* (R^q f_* Y) ≅ R^q b_* (a^* Y)`.
Helpers: `pushPullIso`/`lshPullIso` (`e_* e^* ≅ 𝟭`, `e_! e^* ≅ 𝟭` for an isomorphism `e`), `lshCompIso`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ]

section Iso

end Iso

/-- **Étale base change of `R^q f_*` for a pullback square**: `g^* (R^q f_* Y) ≅ R^q b_* (a^* Y)`. -/
def pullRDerSq {P X V W : Scheme.{u}} {f : P ⟶ X} {g : V ⟶ X} [Etale g] {a : W ⟶ P} {b : W ⟶ V}
    (sq : IsPullback a b f g) (q : ℕ) (Y : EtSh Λ P) :
    (pull g Λ).obj (((push f Λ).rightDerived q).obj Y) ≅ ((push b Λ).rightDerived q).obj ((pull a Λ).obj Y) :=
  (pullIsoRes g Λ).app _ ≪≫ resRDerIso g f q Y ≪≫
    ((push (pullback.fst g f) Λ).rightDerived q).mapIso ((pullIsoRes (pullback.snd g f) Λ).app Y).symm ≪≫
    ((push (pullback.fst g f) Λ).rightDerived q).mapIso (pushPullIso sq.flip.isoPullback.hom _).symm ≪≫
    rightDerivedPushIso sq.flip.isoPullback.hom (pullback.fst g f) b sq.flip.isoPullback_hom_fst q _ ≪≫
    ((push b Λ).rightDerived q).mapIso
      ((pullCompIso Λ sq.flip.isoPullback.hom (pullback.snd g f)).symm.app Y ≪≫
        (pullCongr Λ sq.flip.isoPullback_hom_snd).app Y)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_Bnd =====
section

/-!
# S4-EtLeray, part 9: boundary vanishing for compact supports

* `isZero_lsh_of_isEmpty`: `j_! F = 0` when the source of `j` is empty;
* **`isZero_pull_push_lsh`**: `ι^* i_* j_! F = 0` when no point of `U` meets the image of `ι` in `P`;
* **`isZero_stalk_rder`**: if proper base change holds at `s` (`PBCGood`) and `N` restricts to zero on the fibre
  over `s`, then `(R^q g_* N)_s = 0`;
* **`isIso_counit_of_closed`**: over a scheme of finite type over a field, if the stalks of `M` at the closed
  points off an open `U` vanish, then `j_! j^* M ⟶ M` is an isomorphism.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtLeray

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ]

/-- **Vanishing stalks of `R^q g_* N`** at a point where proper base change holds and `N` restricts to zero
on the fibre. -/
theorem isZero_stalk_rder {P B : Scheme.{u}} (g : P ⟶ B) [UniversallyClosed g] (s : GeomPt B)
    (hg : PBCGood Λ g s) (N : EtSh Λ P) (hN : IsZero ((pull (fibι g s) Λ).obj N)) (q : ℕ) :
    IsZero ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj N)) := by
  obtain ⟨e⟩ := pbc_of_good Λ g s hg N q
  have : Subsingleton ((s.stalkF Λ).obj (((push g Λ).rightDerived q).obj N)) :=
    ⟨fun a b => e.injective ((EtMV.ext_eq_zero_of_isZero (e a) hN).trans
      (EtMV.ext_eq_zero_of_isZero (e b) hN).symm)⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **`j_! j^* M ≅ M`** when the stalks of `M` at the closed points off `U` vanish. -/
theorem isIso_counit_of_closed {K : Type u} [Field K] {X U : Scheme.{u}}
    (gX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gX] (j : U ⟶ X) [IsOpenImmersion j]
    (M : EtSh Λ X) (hM : ∀ x : X, IsClosed ({x} : Set X) → x ∉ Set.range j → IsZero (stalk Λ M x)) :
    IsIso ((lshAdj j Λ).counit.app M) := by
  have : Mono ((lshAdj j Λ).counit.app M) := mono_lshAdj_counit (j := j) (Λ := Λ) M
  have : Epi ((lshAdj j Λ).counit.app M) := by
    refine Preadditive.epi_of_isZero_cokernel _ (isZero_of_closed gX _ fun x hx => ?_)
    by_cases hxU : x ∈ Set.range j
    · obtain ⟨t, rfl⟩ := hxU
      exact StkTr.isZero_cokernel_counit (j := j) (Λ := Λ) M t
    · exact GPtIso.isZero_cokernel (Λ := Λ) (geomPtAt x) _ ((hM x hx hxU).epi _)
  exact isIso_of_mono_of_epi _

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLeray_RelA =====
section

/-!
# S4-EtLeray, part 15: relative one-row Grothendieck, acyclic case and row `1`

`F₁ : C ⥤ D` additive, left exact, preserving injectives; `F₂ : D ⥤ E` additive, left exact.
* `rightDerived_additive`: `R^n F` is additive;
* `mapRes P hN`: for `F₁`-acyclic `N`, `F₁ P` is an injective resolution of `F₁ N`;
* **`acycIso`**: `F₁`-acyclic `N` ⇒ `R^m(F₁ ⋙ F₂) N ≅ R^m F₂ (F₁ N)`;
* `isIso_rder_g`: `R^(m+1) F₂` inverts the epi of a short exact sequence with injective kernel;
* **`row1Iso`**: `F₁ N` injective, `R^q F₁ N = 0` for `q ≥ 2` ⇒ `R^(m+1)(F₁ ⋙ F₂) N ≅ R^m F₂ (R¹ F₁ N)`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLeray

universe v u v' u' v'' u''

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]

section MapRes

variable [HasInjectiveResolutions C]
variable (F1 : C ⥤ D) [F1.Additive] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects]
variable {N : C} (P : InjectiveResolution N)

set_option backward.isDefEq.respectTransparency false in
/-- For `F₁`-acyclic `N`, `F₁ P` is an injective resolution of `F₁ N`. -/
def mapRes (hN : ∀ q : ℕ, IsZero ((F1.rightDerived (q + 1)).obj N)) : InjectiveResolution (F1.obj N) where
  cocomplex := (F1.mapHomologicalComplex _).obj P.cocomplex
  injective q := F1.injective_obj_of_injective (P.injective q)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨F1.map (P.ι.f 0), mapRes_ι_d F1 P⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨P.exact₀.map_of_mono_of_preservesKernel F1 inferInstance inferInstance,
            (inferInstance : Mono (F1.map (P.ι.f 0)))⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans ((mapRes_ι_f0 F1 P).symm.trans (Category.comp_id _).symm))
          ((Category.id_comp _).trans (Category.comp_id _).symm)
      all_goals first | rfl | simp
    · rw [quasiIsoAt_iff_exactAt]
      · rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact (hN _).of_iso (P.isoRightDerivedObj F1 _).symm
      · apply CochainComplex.exactAt_succ_single_obj⟩

theorem mapRes_cocomplex (hN : ∀ q : ℕ, IsZero ((F1.rightDerived (q + 1)).obj N)) :
    (mapRes F1 P hN).cocomplex = (F1.mapHomologicalComplex _).obj P.cocomplex := rfl

end MapRes

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
variable (F1 : C ⥤ D) [F1.Additive] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects]
variable (F2 : D ⥤ E) [F2.Additive] [PreservesFiniteLimits F2]

/-- **Acyclic case**: `R^q F₁ N = 0` for `q ≥ 1` ⇒ `R^m(F₁ ⋙ F₂) N ≅ R^m F₂ (F₁ N)`. -/
def acycIso (N : C) (hN : ∀ q : ℕ, IsZero ((F1.rightDerived (q + 1)).obj N)) (m : ℕ) :
    ((F1 ⋙ F2).rightDerived m).obj N ≅ (F2.rightDerived m).obj (F1.obj N) :=
  (injectiveResolution N).isoRightDerivedObj (F1 ⋙ F2) m ≪≫
    (HomologicalComplex.homologyFunctor E _ m).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F1 ⋙ F2)) _).app _).symm ≪≫
    ((mapRes F1 (injectiveResolution N) hN).isoRightDerivedObj F2 m).symm

variable {N : C} (P : InjectiveResolution N)

omit [HasInjectiveResolutions D] [PreservesFiniteLimits F1] [F1.PreservesInjectiveObjects] in
/-- `R^q F₁ (Qc P) = 0` for `q ≥ 1` when `R^q F₁ N = 0` for `q ≥ 2`. -/
theorem qc_acyc (hN : ∀ q : ℕ, IsZero ((F1.rightDerived (q + 2)).obj N)) (q : ℕ) :
    IsZero ((F1.rightDerived (q + 1)).obj (Qc P)) :=
  (hN q).of_iso (dsIso P F1 q)

end RamanujanPetersson.EtLeray

end

end

-- ===== S4.Def_RP_EtLin_Gen =====
section

/-!
# S4-EtLin, Gen: generic Λ-linearity (adjoints, homology, right derived functors, Ext upgrade lemmas)

* `leftAdjoint_linear` / `rightAdjoint_linear`: an adjoint of a linear functor is linear;
* `homologyMap_smul'`, instance `homologyFunctor_linear'` (`HomologicalComplex.homologyFunctor` is linear);
* instance **`rightDerived_linear`**: `R^n F` is `R`-linear for a linear additive `F`;
* **upgrade lemmas** `ext_map_smul`, `ext_map_smul_nat`, `ext_toMod_smul`, `mod_toExt_smul`: an additive map out
  of `Ext A N n` (or out of `S.obj N` for a linear `S : C ⥤ ModuleCat R`) that is natural in `N` is `R`-linear
  (`Ext.smul_eq_comp_mk₀`); `extLinearMap`, `extLinearEquiv` package them.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLin

universe w w' v u v' u'

section Adj

end Adj

section Homology

end Homology

section RDer

end RDer

section ExtUp

end ExtUp

section ExtMod

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {C' : Type u'} [Category.{v'} C'] [Abelian C'] [Linear R C']

/-- **Upgrade lemma (modules to Ext)**, e.g. maps out of a stalk. -/
theorem mod_toExt_smul {hC' : HasExt.{w} C'} (S : C ⥤ ModuleCat.{w'} R) [S.Linear R] (T : C ⥤ C') [T.Linear R]
    {A' : C'} {m : ℕ} (φ : ∀ N : C, S.obj N →+ Ext A' (T.obj N) m)
    (hφ : ∀ {N N' : C} (f : N ⟶ N') (v : S.obj N),
      φ N' ((S.map f).hom v) = (φ N v).comp (Ext.mk₀ (T.map f)) (add_zero m))
    (r : R) (N : C) (v : S.obj N) : φ N (r • v) = r • φ N v := by
  have h : (S.map (r • 𝟙 N)).hom v = r • v := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [← h, hφ, Functor.map_smul, CategoryTheory.Functor.map_id, ← Ext.smul_eq_comp_mk₀]

end ExtMod

section ExtPack

end ExtPack

end RamanujanPetersson.EtLin

end

end

-- ===== S4.Def_RP_EtLin_ExtL =====
section

/-!
# S4-EtLin, ExtL: `Λ`-linear versions of the basic `Ext` / `H` maps

Generic (any `Λ`-linear abelian category, `HasExt` implicit): `extIsoLeftL`, `extIsoRightL`, `extAdjMap_smul`,
`extAdjEquivL` (for `L ⊣ R` with `R` linear). Étale: `HmapL`, `HisoL`. Each `…L` has `…L_apply` (`rfl`) to the
additive original.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtLin

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe w v u v' u'

section Gen

variable {Λ : Type*} [Ring Λ] {C : Type u} [Category.{v} C] [Abelian C] [Linear Λ C] {hC : HasExt.{w} C}

variable (Λ) in
/-- `extIsoLeft` is `Λ`-linear. -/
def extIsoLeftL {A A' : C} (e : A ≅ A') (B : C) (n : ℕ) : Ext A' B n ≃ₗ[Λ] Ext A B n :=
  (extIsoLeft e B n).toLinearEquiv (fun r x => Ext.comp_smul _ x (zero_add n) r)

theorem extIsoLeftL_apply {A A' : C} (e : A ≅ A') (B : C) (n : ℕ) (x : Ext A' B n) :
    extIsoLeftL Λ e B n x = extIsoLeft e B n x :=
  rfl

end Gen

section Adj

end Adj

section Et

variable (Λ : Type u) [CommRing Λ] {X : AlgebraicGeometry.Scheme.{u}}

/-- `H^n(X, -)` on morphisms, `Λ`-linearly. -/
def HmapL {F G : EtSh Λ X} (φ : F ⟶ G) (n : ℕ) : H Λ F n →ₗ[Λ] H Λ G n where
  toFun := Hmap Λ φ n
  map_add' := (Hmap Λ φ n).map_add
  map_smul' r x := Ext.smul_comp x _ (add_zero n) r

end Et

end RamanujanPetersson.EtLin

end

end


