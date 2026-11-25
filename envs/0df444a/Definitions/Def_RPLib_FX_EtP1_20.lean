-- Prove2me | Definitions.Def_RPLib_FX_EtP1_20
-- name    : RPLib_FX_EtP1_20
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:19:52.073841+00:00
-- url     : https://prove2.me/theorems/1d5d2668-5b54-4686-bbe4-6b83200d204c
-- title:
--   Étale cohomology of the projective line, library file 20 of 34
-- statement:
--   File 20 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
--   * `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--   * `S4.Def_RP_EtCompact_Glue`: S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)
--   * `S4.Def_RP_EtCompact_MVSplit`: S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)
--   * `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
--   * `S4.Def_RP_EtCompact_P1H1`: S4-EtCompact, part 35: `H^1(P^1, Λ) = 0` and `H^1_c(A^1, Λ) = 0` (O8b, file 5)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_10

/-!
# Étale cohomology of the projective line, library file 20 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
* `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
* `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
* `S4.Def_RP_EtCompact_Glue`: S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)
* `S4.Def_RP_EtCompact_MVSplit`: S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)
* `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
* `S4.Def_RP_EtCompact_P1H1`: S4-EtCompact, part 35: `H^1(P^1, Λ) = 0` and `H^1_c(A^1, Λ) = 0` (O8b, file 5)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_CutMap =====
section

/-!
# S4-EtCompact, part 4: maps between cut sheaves

For opens `W' ≤ W` the inclusion `j_{W'!} G|_{W'} ⟶ j_{W!} G|_W` (`openCutLe`, the lift of
`openCutι W'` through the monomorphism `openCutι W`), for opens `V ≤ V'` the quotient map
`G / j_{V!} ⟶ G / j_{V'!}` (`quotCutLe`), functoriality `openCutMap`, and their stalks.
`cutWV W V F := j_{W!}(F / j_{V!} F|_V)|_W` is `F` cut to `W ∩ Vᶜ`; its stalks are
`F_x` for `x ∈ W \ V` and `0` otherwise.
All identities are checked on stalks at the points `geomPtAt x`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section OpenLe

variable {W W' : X.Opens} (h : W' ≤ W)

end OpenLe

section QuotLe

variable {V V' : X.Opens} (h : V ≤ V')

end QuotLe

section OpenMap

variable (W : X.Opens)

/-- Functoriality of `openCut W`. -/
def openCutMap {G G' : EtSh Λ X} (φ : G ⟶ G') : openCut Λ W G ⟶ openCut Λ W G' :=
  (lsh W.ι Λ).map ((res W.ι Λ).map φ)

@[reassoc (attr := simp)]
theorem openCutMap_comp {G G' : EtSh Λ X} (φ : G ⟶ G') :
    openCutMap W φ ≫ openCutι Λ W G' = openCutι Λ W G ≫ φ :=
  (lshAdj W.ι Λ).counit.naturality φ

end OpenMap

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_CutFun =====
section

/-!
# S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable

`quotFunctor V : F ↦ F / j_{V!} F|_V` and `cutWVFunctor W V = quotFunctor V ⋙ res ⋙ lsh` (whose
value at `F` is `cutWV W V F` by definition) are exact: `quotFunctor` is checked on stalks, the
other two factors are exact by `Def_RP_EtCompact_Exact`. Hence a short exact sequence
`0 → F' → F → F'' → 0` gives the long exact sequence
`… → H^n_c(S, F') → H^n_c(S, F) → H^n_c(S, F'') → H^(n+1)_c(S, F') → …`
(E0Probe amendment A7).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Quot

variable (V : X.Opens)

end Quot

instance lsh_preservesFiniteColimits' {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteColimits (lsh j Λ) :=
  inferInstance

section SheafLES

variable (W V : X.Opens) {S : ShortComplex (EtSh Λ X)} (hS : S.ShortExact)

include hS

end SheafLES

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H0 =====
section

/-!
# S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)

* `smulEnd r F : F ⟶ F` (multiplication by `r : Λ`); its stalk maps are `r • 𝟙` (`stalk_smulEnd`).
* `exists_lift_unitSh`: if `ρ : A ⟶ B` is epi, `A ≅ Λ_X` and `B` has zero stalks off one point `x0`, every
  `ψ : Λ_X ⟶ B` lifts through `ρ` (stalk at `x0` is cyclic on `1`).
* `resC_zero_surjective`: `H^0_c(S) → H^0_c(S \ O)` is onto when `cut S F ≅ Λ_X` and `S \ O` is at most a point;
  hence `extO` is injective in degree `1` (`extO_one_injective_of`).
* `P1.hcA1_zero_eq_zero`, **`A1.hc_zero_eq_zero`**: `H^0_c(A^1, Λ) = 0` (any field).
* **`A1.hcEquivP1One`**: `H^1_c(A^1, Λ) ≃+ H^1(P^1, Λ)` (`K` algebraically closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Smul

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- Multiplication by `r : Λ` on an etale sheaf of `Λ`-modules. -/
def smulEnd (r : Λ) (F : EtSh Λ X) : F ⟶ F :=
  ObjectProperty.homMk (r • 𝟙 F.obj)

theorem stalk_smulEnd (s : GeomPt X) (r : Λ) (F : EtSh Λ X) :
    (s.stalkF Λ).map (smulEnd r F) = r • 𝟙 _ := by
  change s.point.presheafFiber.map (r • 𝟙 F.obj) = r • 𝟙 _
  refine s.point.presheafFiber_hom_ext (fun U x => ?_)
  simp only [GrothendieckTopology.Point.toPresheafFiber_naturality, NatTrans.app_smul, NatTrans.id_app,
    Linear.smul_comp, Category.id_comp]
  exact ((Linear.comp_smul _ _ _ _ r (𝟙 _)).trans (congrArg (fun g => r • g) (Category.comp_id _))).symm

theorem smulEnd_stalk_apply (s : GeomPt X) (r : Λ) (F : EtSh Λ X) (v : (s.stalkF Λ).obj F) :
    ((s.stalkF Λ).map (smulEnd r F)).hom v = r • v := by
  rw [stalk_smulEnd, ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply]

end Smul

section Lift

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- The element `1 ∈ (Λ_X)_x̄ ≅ Λ`. -/
def oneAt (x : X) : ((geomPtAt x).stalkF Λ).obj (unitSh Λ X) :=
  (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom (1 : Λ)

theorem unitSh_stalk_hom_ext (x : X) {N : ModuleCat.{u} Λ}
    {f g : ((geomPtAt x).stalkF Λ).obj (unitSh Λ X) ⟶ N} (h : f.hom (oneAt Λ x) = g.hom (oneAt Λ x)) :
    f = g := by
  rw [← cancel_epi (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  exact h

theorem smul_oneAt (x : X) (a : ((geomPtAt x).stalkF Λ).obj (unitSh Λ X)) :
    (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom a • oneAt Λ x = a := by
  have h1 : (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom
      ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom a) = a := by
    rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  conv_rhs => rw [← h1]
  rw [oneAt, ← map_smul]
  congr 1
  exact mul_one _

end Lift

section Res

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Res

section P1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Glue =====
section

/-!
# S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)

* `comp_quotCutπ_inf`: a map into `G` factoring through `j_{U!}G|_U` and `j_{V!}G|_V` factors through `j_{U⊓V!}`.
* **`exists_glue`**: for opens `U, V` covering `X`, maps `φ_U : j_{U!}F|_U ⟶ G`, `φ_V : j_{V!}F|_V ⟶ G` agreeing on
  `j_{U⊓V!}F|_{U⊓V}` glue to `φ : F ⟶ G` (Mayer-Vietoris: `j_{U!} ⊞ j_{V!} ⟶ F` is epi with kernel `j_{U⊓V!}`).
* **`eq_smulEnd`**: on a connected `X`, every `φ : Λ_X ⟶ Λ_X` is multiplication by a scalar.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Glue

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- **Gluing along a Zariski cover `X = U ∪ V`.** -/
theorem exists_glue {F G : EtSh Λ X} {U V : X.Opens} (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (φU : openCut Λ U F ⟶ G) (φV : openCut Λ V F ⟶ G)
    (h : openCutLe (inf_le_left : U ⊓ V ≤ U) F ≫ φU = openCutLe (inf_le_right : U ⊓ V ≤ V) F ≫ φV) :
    ∃ φ : F ⟶ G, openCutι Λ U F ≫ φ = φU ∧ openCutι Λ V F ≫ φ = φV := by
  have hπ : Epi (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) := epi_biprod_desc_openCutι hUV
  have hmU : Mono (openCutι Λ U F) := mono_openCutι _ _
  have hmV : Mono (openCutι Λ V F) := mono_openCutι _ _
  have hψ : kernel.ι (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) ≫ biprod.desc φU φV = 0 := by
    obtain ⟨a, ha⟩ : ∃ a, a = kernel.ι (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) ≫ biprod.fst :=
      ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = kernel.ι (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) ≫ biprod.snd :=
      ⟨_, rfl⟩
    have hab : a ≫ openCutι Λ U F + b ≫ openCutι Λ V F = 0 := by
      have h0 : kernel.ι (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) ≫
          (biprod.fst ≫ openCutι Λ U F + biprod.snd ≫ openCutι Λ V F) = 0 := by
        rw [← biprod.desc_eq]
        exact kernel.condition _
      rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← ha, ← hb] at h0
      exact h0
    have hb' : (-b) ≫ openCutι Λ V F = a ≫ openCutι Λ U F := by
      rw [Preadditive.neg_comp, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]
      exact hab
    have hq := comp_quotCutπ_inf (a ≫ openCutι Λ U F) a rfl (-b) hb'
    obtain ⟨c, hc⟩ : ∃ c : _ ⟶ openCut Λ (U ⊓ V) F, c ≫ openCutι Λ (U ⊓ V) F = a ≫ openCutι Λ U F :=
      ⟨Abelian.monoLift (openCutι Λ (U ⊓ V) F) (a ≫ openCutι Λ U F) hq, Abelian.monoLift_comp _ _ _⟩
    have hca : c ≫ openCutLe (inf_le_left : U ⊓ V ≤ U) F = a := by
      rw [← cancel_mono (openCutι Λ U F), Category.assoc, openCutLe_comp, hc]
    have hcb : c ≫ openCutLe (inf_le_right : U ⊓ V ≤ V) F = -b := by
      rw [← cancel_mono (openCutι Λ V F), Category.assoc, openCutLe_comp, hc, hb']
    rw [show biprod.desc φU φV = biprod.fst ≫ φU + biprod.snd ≫ φV from biprod.desc_eq,
      Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← ha, ← hb, ← hca,
      ← neg_neg b, ← hcb, Preadditive.neg_comp, Category.assoc, Category.assoc, h, add_neg_cancel]
  refine ⟨Abelian.epiDesc _ _ hψ, ?_, ?_⟩
  · calc openCutι Λ U F ≫ Abelian.epiDesc _ _ hψ
        = biprod.inl ≫ (biprod.desc (openCutι Λ U F) (openCutι Λ V F) ≫ Abelian.epiDesc _ _ hψ) := by
          rw [← Category.assoc, biprod.inl_desc]
      _ = φU := by rw [Abelian.comp_epiDesc, biprod.inl_desc]
  · calc openCutι Λ V F ≫ Abelian.epiDesc _ _ hψ
        = biprod.inr ≫ (biprod.desc (openCutι Λ U F) (openCutι Λ V F) ≫ Abelian.epiDesc _ _ hψ) := by
          rw [← Category.assoc, biprod.inr_desc]
      _ = φV := by rw [Abelian.comp_epiDesc, biprod.inr_desc]

end Glue

section Scalar

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- **Endomorphisms of `Λ_X` on a connected `X` are scalars** (the scalar read off at any point `x0`). -/
theorem eq_smulEnd [PreconnectedSpace X] (φ : unitSh Λ X ⟶ unitSh Λ X) (x0 : X) :
    φ = smulEnd ((constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)).hom.hom
      ((((geomPtAt x0).stalkF Λ).map φ).hom (oneAt Λ x0))) (unitSh Λ X) :=
  stalk_faithful (isLisse_unitSh (Λ := Λ) (X := X)) (isLisse_unitSh (Λ := Λ) (X := X)).isLocConst (geomPtAt x0)
    (unitSh_stalk_hom_ext Λ x0 (by rw [smulEnd_stalk_apply, smul_oneAt]))

theorem exists_eq_smulEnd [PreconnectedSpace X] [Nonempty X] (φ : unitSh Λ X ⟶ unitSh Λ X) :
    ∃ r : Λ, φ = smulEnd r (unitSh Λ X) :=
  ⟨_, eq_smulEnd Λ φ (Classical.arbitrary X)⟩

end Scalar

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_MVSplit =====
section

/-!
# S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)

* `smulEnd_comp`, `res_map_smulEnd`: scalars commute with all maps and with restriction.
* `openCut_unitSh_ext`: on a connected nonempty open `W`, every `j_{W!}Λ|_W ⟶ Λ_X` is `ι ≫ (r • ·)`.
* `splits_of_cover`: a short exact sequence that splits over `U` and over `V` (with the overlap
  extension property) splits.
* **`subsingleton_h1_of_cover`**: if `X = U ∪ V` (open immersions `j_U, j_V`), `U ∩ V` is connected and
  nonempty, and `H^1(U, Λ) = H^1(V, Λ) = 0`, then `H^1(X, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Scal

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem smulEnd_comp (r : Λ) {F G : EtSh Λ X} (φ : F ⟶ G) : smulEnd r F ≫ φ = φ ≫ smulEnd r G := by
  refine hom_ext_stalk Λ (fun x => ?_)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, stalk_smulEnd, stalk_smulEnd,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

theorem res_map_smulEnd {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (r : Λ) (F : EtSh Λ X) :
    (res j Λ).map (smulEnd r F) = smulEnd r ((res j Λ).obj F) := by
  refine hom_ext_stalk Λ (fun x => ?_)
  have h := (resStalkIso j Λ (geomPtAt x)).hom.naturality (smulEnd r F)
  rw [CategoryTheory.Functor.comp_map, stalk_smulEnd, Linear.comp_smul, Category.comp_id] at h
  rw [(Iso.eq_comp_inv ((resStalkIso j Λ (geomPtAt x)).app F)).2 h, Linear.smul_comp, Iso.app_inv,
    Iso.hom_inv_id_app, stalk_smulEnd]
  rfl

/-- **Maps `j_{W!}Λ|_W ⟶ Λ_X` on a connected nonempty open `W` are scalars.** -/
theorem openCut_unitSh_ext (W : X.Opens) [PreconnectedSpace W.toScheme] [Nonempty W.toScheme]
    (m : openCut Λ W (unitSh Λ X) ⟶ unitSh Λ X) :
    ∃ r : Λ, openCutι Λ W (unitSh Λ X) ≫ smulEnd r (unitSh Λ X) = m := by
  obtain ⟨r, hr⟩ := exists_eq_smulEnd Λ
    ((resUnitIsoOf (Λ := Λ) W.ι).inv ≫ (lshAdj W.ι Λ).homEquiv _ _ m ≫ (resUnitIsoOf (Λ := Λ) W.ι).hom)
  refine ⟨r, ?_⟩
  have h1 : (lshAdj W.ι Λ).homEquiv _ _ m = (res W.ι Λ).map (smulEnd r (unitSh Λ X)) := by
    rw [res_map_smulEnd]
    calc (lshAdj W.ι Λ).homEquiv _ _ m
        = (resUnitIsoOf (Λ := Λ) W.ι).hom ≫ ((resUnitIsoOf (Λ := Λ) W.ι).inv ≫
            (lshAdj W.ι Λ).homEquiv _ _ m ≫ (resUnitIsoOf (Λ := Λ) W.ι).hom) ≫
              (resUnitIsoOf (Λ := Λ) W.ι).inv := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
      _ = smulEnd r _ := by rw [hr, smulEnd_comp, Iso.hom_inv_id_assoc]
  rw [← ((lshAdj W.ι Λ).homEquiv _ _).symm_apply_apply m, h1, Adjunction.homEquiv_counit]
  exact (openCutMap_comp W (smulEnd r (unitSh Λ X))).symm

end Scal

section Split

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem openCutMap_openCutLe {W W' : X.Opens} (h : W' ≤ W) {G G' : EtSh Λ X} (φ : G ⟶ G') :
    openCutMap W' φ ≫ openCutLe h G' = openCutLe h G ≫ openCutMap W φ := by
  rw [← cancel_mono (openCutι Λ W G'), Category.assoc, Category.assoc, openCutLe_comp, openCutMap_comp,
    openCutMap_comp, openCutLe_comp_assoc]

theorem glue_ext {F G : EtSh Λ X} {U V : X.Opens} (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) {f g : F ⟶ G}
    (hU : openCutι Λ U F ≫ f = openCutι Λ U F ≫ g) (hV : openCutι Λ V F ≫ f = openCutι Λ V F ≫ g) :
    f = g := by
  have hπ : Epi (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) := epi_biprod_desc_openCutι hUV
  rw [← cancel_epi (biprod.desc (openCutι Λ U F) (openCutι Λ V F))]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc_assoc, biprod.inl_desc_assoc, hU]
  · rw [biprod.inr_desc_assoc, biprod.inr_desc_assoc, hV]

/-- **Splitting along a cover.** A short exact sequence whose first map has retractions over `U` and `V`
splits, provided maps `j_{U⊓V!}X₃ ⟶ X₁` extend to `X₃ ⟶ X₁`. -/
theorem splits_of_cover {S : ShortComplex (EtSh Λ X)} (hS : S.ShortExact) {U V : X.Opens}
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V)
    (φU : openCut Λ U S.X₂ ⟶ S.X₁) (hU : openCutMap U S.f ≫ φU = openCutι Λ U S.X₁)
    (φV : openCut Λ V S.X₂ ⟶ S.X₁) (hV : openCutMap V S.f ≫ φV = openCutι Λ V S.X₁)
    (hW : ∀ m : openCut Λ (U ⊓ V) S.X₃ ⟶ S.X₁, ∃ n : S.X₃ ⟶ S.X₁, openCutι Λ (U ⊓ V) S.X₃ ≫ n = m) :
    ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ := by
  have hT := hS.map_of_exact (res (U ⊓ V).ι Λ ⋙ lsh (U ⊓ V).ι Λ)
  have hTe : Epi (S.map (res (U ⊓ V).ι Λ ⋙ lsh (U ⊓ V).ι Λ)).g := hT.epi_g
  obtain ⟨d, hd⟩ : ∃ d, d = openCutLe (inf_le_left : U ⊓ V ≤ U) S.X₂ ≫ φU -
      openCutLe (inf_le_right : U ⊓ V ≤ V) S.X₂ ≫ φV := ⟨_, rfl⟩
  have hfd : openCutMap (U ⊓ V) S.f ≫ d = 0 := by
    rw [hd, Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, openCutMap_openCutLe,
      openCutMap_openCutLe, Category.assoc, Category.assoc, hU, hV, openCutLe_comp, openCutLe_comp, sub_self]
  obtain ⟨m, hm⟩ : ∃ m, openCutMap (U ⊓ V) S.g ≫ m = d := ⟨hT.exact.desc d hfd, hT.exact.g_desc d hfd⟩
  obtain ⟨n, hn⟩ := hW m
  have key : openCutLe (inf_le_right : U ⊓ V ≤ V) S.X₂ ≫ openCutι Λ V S.X₂ ≫ S.g ≫ n = d := by
    rw [← Category.assoc, openCutLe_comp, ← openCutMap_comp_assoc, hn, hm]
  obtain ⟨r, hrU, hrV⟩ := exists_glue hUV φU (φV + openCutι Λ V S.X₂ ≫ S.g ≫ n) (by
    rw [Preadditive.comp_add, key, hd]
    abel)
  refine ⟨r, glue_ext hUV ?_ ?_⟩
  · rw [Category.comp_id, ← Category.assoc, ← openCutMap_comp, Category.assoc, hrU, hU]
  · rw [Category.comp_id, ← Category.assoc, ← openCutMap_comp, Category.assoc, hrV, Preadditive.comp_add, hV,
      openCutMap_comp_assoc, S.zero_assoc, zero_comp, comp_zero, add_zero]

end Split

section Charts

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem lshToOpenCut_natural {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {G G' : EtSh Λ X}
    (φ : G ⟶ G') :
    (lsh j Λ).map ((res j Λ).map φ) ≫ lshToOpenCut j G' = lshToOpenCut j G ≫ openCutMap j.opensRange φ := by
  rw [← cancel_mono (openCutι Λ j.opensRange G'), Category.assoc, Category.assoc, lshToOpenCut_comp,
    openCutMap_comp, lshToOpenCut_comp_assoc]
  exact (lshAdj j Λ).counit.naturality φ

/-- A retraction of `j^* S.f` gives a retraction of `S.f` over `range j`. -/
theorem exists_openCut_retraction {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    {S : ShortComplex (EtSh Λ X)} (r : (res j Λ).obj S.X₂ ⟶ (res j Λ).obj S.X₁)
    (hr : (res j Λ).map S.f ≫ r = 𝟙 _) :
    ∃ φ : openCut Λ j.opensRange S.X₂ ⟶ S.X₁,
      openCutMap j.opensRange S.f ≫ φ = openCutι Λ j.opensRange S.X₁ := by
  refine ⟨inv (lshToOpenCut j S.X₂) ≫ (lsh j Λ).map r ≫ (lshAdj j Λ).counit.app S.X₁, ?_⟩
  rw [← cancel_epi (lshToOpenCut j S.X₁), ← Category.assoc, ← lshToOpenCut_natural, Category.assoc,
    IsIso.hom_inv_id_assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hr,
    CategoryTheory.Functor.map_id, Category.id_comp, lshToOpenCut_comp]

/-- If `H^1(Y, Λ) = 0`, an extension of `Λ_X` by `Λ_X` splits after restriction to `Y`. -/
theorem exists_res_retraction {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hY : Subsingleton (H Λ (unitSh Λ Y) 1)) {S : ShortComplex (EtSh Λ X)} (hS : S.ShortExact)
    (e1 : S.X₁ ≅ unitSh Λ X) (e3 : S.X₃ ≅ unitSh Λ X) :
    ∃ r : (res j Λ).obj S.X₂ ⟶ (res j Λ).obj S.X₁, (res j Λ).map S.f ≫ r = 𝟙 _ := by
  have hS' := hS.map_of_exact (res j Λ)
  let T : Ext ((res j Λ).obj S.X₃) ((res j Λ).obj S.X₁) 1 ≃+ H Λ (unitSh Λ Y) 1 :=
    (extIsoLeft ((resUnitIsoOf j).symm ≪≫ ((res j Λ).mapIso e3).symm) _ 1).trans
      (extIsoRight _ ((res j Λ).mapIso e1 ≪≫ resUnitIsoOf j) 1)
  exact (extClass_eq_zero_iff hS').1 (T.injective (Subsingleton.elim _ _))

/-- **`H^1` from two charts**: `X = U ∪ V` with `U ∩ V` connected and nonempty, `H^1(U, Λ) = H^1(V, Λ) = 0`
imply `H^1(X, Λ) = 0`. -/
theorem subsingleton_h1_of_cover {YU YV : Scheme.{u}} (jU : YU ⟶ X) (jV : YV ⟶ X) [IsOpenImmersion jU]
    [IsOpenImmersion jV] (hUV : ∀ x : X, x ∈ jU.opensRange ∨ x ∈ jV.opensRange)
    [PreconnectedSpace (jU.opensRange ⊓ jV.opensRange).toScheme]
    [Nonempty (jU.opensRange ⊓ jV.opensRange).toScheme]
    (hU : Subsingleton (H Λ (unitSh Λ YU) 1)) (hV : Subsingleton (H Λ (unitSh Λ YV) 1)) :
    Subsingleton (H Λ (unitSh Λ X) 1) := by
  suffices h : ∀ e : H Λ (unitSh Λ X) 1, e = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro e
  obtain ⟨s, hs⟩ := exists_extClass_eq e
  have hS := pbSES_shortExact s
  rw [← hs]
  refine (extClass_eq_zero_iff hS).2 ?_
  obtain ⟨rU, hrU⟩ := exists_res_retraction jU hU hS (Iso.refl (unitSh Λ X)) (Iso.refl (unitSh Λ X))
  obtain ⟨rV, hrV⟩ := exists_res_retraction jV hV hS (Iso.refl (unitSh Λ X)) (Iso.refl (unitSh Λ X))
  obtain ⟨φU, hφU⟩ := exists_openCut_retraction jU rU hrU
  obtain ⟨φV, hφV⟩ := exists_openCut_retraction jV rV hrV
  exact splits_of_cover hS hUV φU hφU φV hφV (fun m => by
    obtain ⟨r, hr⟩ := openCut_unitSh_ext (jU.opensRange ⊓ jV.opensRange) m
    exact ⟨_, hr⟩)

end Charts

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Cover =====
section

/-!
# S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)

* `dehom' = dehom ∘ swap` (`X₁ ↦ 1`, `X₀ ↦ t`), `awayDehom' : K[X₀, X₁]_(X₁) ≃ K[t]`, the chart
  `chartA1' : A^1_K ⟶ P^1_K` (`t ↦ [t : 1]`) with range `D₊(X₁)`.
* `P1.cover`: the two charts cover `P^1`; their overlap is nonempty and connected (`P^1` irreducible).
* **`P1.subsingleton_h1`**: `H^1(A^1, Λ) = 0 ⇒ H^1(P^1, Λ) = 0` (`subsingleton_h1_of_cover`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Chart1

variable {K : Type u} [Field K]

end Chart1

section Cover

variable (K : Type u) [Field K]

theorem P1.genPt_mem_range' : P1.genPt K ∈ (chartA1' K).opensRange := by
  rw [P1.opensRange_chartA1', Proj.mem_basicOpen, P1.genPt_ideal, ← HomogeneousIdeal.mem_iff,
    HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  exact P1.X_ne_zero K 1

instance P1.nonempty_inter : Nonempty ((chartA1 K).opensRange ⊓ (chartA1' K).opensRange).toScheme :=
  ⟨(⟨P1.genPt K, TopologicalSpace.Opens.mem_inf.2 ⟨P1.genPt_mem_range K, P1.genPt_mem_range' K⟩⟩ :
    ((chartA1 K).opensRange ⊓ (chartA1' K).opensRange : (P1 K).Opens))⟩

instance P1.preconnected_inter :
    PreconnectedSpace ((chartA1 K).opensRange ⊓ (chartA1' K).opensRange).toScheme := by
  have h : _root_.IsPreconnected (((chartA1 K).opensRange ⊓ (chartA1' K).opensRange : (P1 K).Opens) : Set (P1 K)) :=
    ((IrreducibleSpace.isIrreducible_univ (P1 K)).isPreirreducible.open_subset
      ((chartA1 K).opensRange ⊓ (chartA1' K).opensRange).isOpen (Set.subset_univ _)).isPreconnected
  exact Subtype.preconnectedSpace h

/-- **`H^1(A^1, Λ) = 0 ⇒ H^1(P^1, Λ) = 0`.** -/
theorem P1.subsingleton_h1 {Λ : Type u} [CommRing Λ] (hA : Subsingleton (H Λ (unitSh Λ (A1 K)) 1)) :
    Subsingleton (H Λ (unitSh Λ (P1 K)) 1) :=
  subsingleton_h1_of_cover (chartA1 K) (chartA1' K) (P1.cover K) hA hA

end Cover

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H1 =====
section

/-!
# S4-EtCompact, part 35: `H^1(P^1, Λ) = 0` and `H^1_c(A^1, Λ) = 0` (O8b, file 5)

`K` algebraically closed, `N • Λ = 0`, `N` invertible in `K`:

* **`P1.h1_subsingleton`**: `H^1(P^1_K, Λ) = 0` (two charts, `H^1(A^1_K, Λ) = 0` by Kummer theory);
* **`A1.hc_one_subsingleton`**, `A1.hc_one_eq_zero`: `H^1_c(A^1_K, Λ) = 0` (`A1.hcEquivP1One`).
-/

set_option autoImplicit false

open AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

variable (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] {N : ℕ}

/-- **`H^1(P^1_K, Λ) = 0`.** -/
theorem P1.h1_subsingleton (hN : (N : K) ≠ 0) (hΛ : (N : Λ) = 0) :
    Subsingleton (H Λ (unitSh Λ (P1 K)) 1) :=
  P1.subsingleton_h1 K (A1.subsingleton_h1 K hN hΛ)

end RamanujanPetersson.EtCompact

end

end


