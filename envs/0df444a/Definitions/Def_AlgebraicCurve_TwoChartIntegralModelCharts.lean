-- Prove2me | Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
-- name    : AlgebraicCurve_TwoChartIntegralModelCharts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d01e58d8-188a-540c-9814-a89d484d5a86
-- title:
--   Chart coordinates j, 1/j on the two-chart integral model
-- statement:
--   Throughout, $R$ is a commutative ring, $F$ a field that is an $R$-algebra and $j \in F$ a nonzero element, and $\mathfrak X = \mathrm{TwoChartIntegralModel}\,R\,F\,j$ is the pushout of $\operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\mathrm{fin}}$ and $\operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\mathrm{inf}}$, where $A_{\mathrm{fin}}$, $A_{\mathrm{inf}}$, $A_{\mathrm{mid}}$ are the subalgebras of $F$ of elements integral over $R[j]$, $R[j^{-1}]$, $R[j,j^{-1}]$ respectively, and $\mathrm{chartFinOpen}$, $\mathrm{chartInfOpen}$ are the open ranges of the two chart immersions. The auxiliary part of the module works on the images $U$, $V$ of $\top$ under these immersions: the overlap immersion $\iota_{\mathrm{mid}}$ is $f_{\mathrm{fin}}$ followed by $\iota_{\mathrm{fin}}$ (equivalently, by the pushout condition, $f_{\mathrm{inf}}$ followed by $\iota_{\mathrm{inf}}$); the images of $f_{\mathrm{fin}}$, $f_{\mathrm{inf}}$ are the basic opens of $j$ and of $j^{-1}$ in the two affine charts, since $A_{\mathrm{mid}}$ is the corresponding localisation away from these elements; two points of the charts have equal image in $\mathfrak X$ exactly when they come from a common point of $\operatorname{Spec} A_{\mathrm{mid}}$; consequently $U \cap V$ is the open range of $\iota_{\mathrm{mid}}$. The sections $f \in \Gamma(\mathfrak X, U)$ and $g \in \Gamma(\mathfrak X, V)$ transport $j \in A_{\mathrm{fin}}$ and $j^{-1} \in A_{\mathrm{inf}}$ through $\mathrm{Spec}$–$\Gamma$ duality and the chart isomorphisms.
--
--   Restricting these along $\mathrm{chartFinOpen} \le U$, $\mathrm{chartInfOpen} \le V$ defines `jCoord` and `jInvCoord`, with $\mathrm{chartFinOpen} \cap \mathrm{chartInfOpen}$ equal to the basic open of either one, and the product of their restrictions to that intersection equal to $1$. For an $R$-algebra $S$, with $\mathfrak X_S$ the pullback of $\mathfrak X \to \operatorname{Spec} R$ along $\operatorname{Spec} S \to \operatorname{Spec} R$: the projection $\mathfrak X_S \to \mathfrak X$ is affine, `chartFinOpenBC`, `chartInfOpenBC` are the preimages of the two chart opens (affine, and covering $\mathfrak X_S$), `jCoordBC`, `jInvCoordBC` are the pullbacks of the coordinates, with the same basic-open and product identities; `constSection` sends $c \in S$ to the global section of $\mathfrak X_S$ obtained from $c$ along $\mathfrak X_S \to \operatorname{Spec} S$, compatibly with differences and preserving units of $S$. Finally `jNeLocus R F j S c` is the open $D(\,j - \bar c\,) \cup D(\,1 - \bar c\cdot j^{-1}\,)$, the union of the basic open of $\mathrm{jCoordBC} - \bar c$ in the finite chart and of $1 - \bar c\cdot \mathrm{jInvCoordBC}$ in the chart at infinity, i.e. the locus on which the coordinate differs from $c$. Several small lemmas on composing restriction maps and on images of open ranges are included as bookkeeping.
--
--   **Relation to Mathlib.** The scheme-theoretic input is Mathlib's (pushouts along locally directed spans, open immersions, basic opens, `Scheme.ΓSpecIso`, `Scheme.Hom.appLE`, pullbacks and affine morphisms); the coordinates `jCoord`, `jInvCoord`, their base changes, `constSection` and the open `jNeLocus` are the project's own vocabulary for this model.
--
--   **Where it is used.** These sections and opens are the chart vocabulary used for the base changes and fibres of the two-chart integral model: `jNeLocus` isolates, over a given $R$-algebra, the locus where the coordinate avoids a prescribed value, which is what feeds the constructions of two-element affine open covers of such base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_TwoChartIntegralModelCharts.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

namespace AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux

variable (R₀ : Type u) [CommRing R₀] (F : Type u) [Field F] [Algebra R₀ F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X₀" => AlgebraicCurve.TwoChartIntegralModel R₀ F j

theorem ιFin_eq_ιInf_iff (x₀ : XFin R₀ F j) (xi : XInf R₀ F j) :
    (ιFin R₀ F j).base x₀ = (ιInf R₀ F j).base xi ↔
      ∃ u : XMid R₀ F j, (fFin R₀ F j).base u = x₀ ∧ (fInf R₀ F j).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R₀ F j) (fInf R₀ F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      exact ⟨u, h₁, h₂⟩
    · rcases fj with ⟨⟩
    · rcases fi with ⟨⟩
  · rintro ⟨u, rfl, rfl⟩
    change (fFin R₀ F j ≫ ιFin R₀ F j).base u = (fInf R₀ F j ≫ ιInf R₀ F j).base u
    rw [glue_condition]

theorem range_fFin : Set.range (fFin R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R₀ F j))) :
      Set (PrimeSpectrum (chartAlgFin R₀ F j))) := by
  letI := (inclFin R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jChartFin R₀ F j)

theorem range_fInf : Set.range (fInf R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R₀ F j))) :
      Set (PrimeSpectrum (chartAlgInf R₀ F j))) := by
  letI := (inclInf R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jInvChartInf R₀ F j)

abbrev ιMid : XMid R₀ F j ⟶ X₀ := fFin R₀ F j ≫ ιFin R₀ F j

theorem isOpenImmersion_ιMid : IsOpenImmersion (ιMid R₀ F j) := inferInstance

theorem ιMid_eq' : ιMid R₀ F j = fInf R₀ F j ≫ ιInf R₀ F j := glue_condition R₀ F j

theorem inclFin_j_mul_inclInf_jInv :
    inclFin R₀ F j (jChartFin R₀ F j) * inclInf R₀ F j (jInvChartInf R₀ F j) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ (j_ne_zero j)])

abbrev U : (X₀).Opens := (ιFin R₀ F j) ''ᵁ ⊤

abbrev V : (X₀).Opens := (ιInf R₀ F j) ''ᵁ ⊤

theorem U_eq : U R₀ F j = chartFinOpen R₀ F j := (ιFin R₀ F j).image_top_eq_opensRange
theorem V_eq : V R₀ F j = chartInfOpen R₀ F j := (ιInf R₀ F j).image_top_eq_opensRange

def sF : Γ(XFin R₀ F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R₀ F j))).inv (jChartFin R₀ F j)

def sI : Γ(XInf R₀ F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R₀ F j))).inv (jInvChartInf R₀ F j)

def f : Γ(X₀, U R₀ F j) := ((ιFin R₀ F j).appIso ⊤).inv (sF R₀ F j)

def g : Γ(X₀, V R₀ F j) := ((ιInf R₀ F j).appIso ⊤).inv (sI R₀ F j)

theorem basicOpen_sF : (XFin R₀ F j).basicOpen (sF R₀ F j) = (fFin R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sF, basicOpen_eq_of_affine]
  exact (range_fFin R₀ F j).symm

theorem basicOpen_sI : (XInf R₀ F j).basicOpen (sI R₀ F j) = (fInf R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sI, basicOpen_eq_of_affine]
  exact (range_fInf R₀ F j).symm

theorem image_opensRange {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a]
    [IsOpenImmersion b] :
    b ''ᵁ a.opensRange = (a ≫ b).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (Scheme.Hom.comp_apply a b u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a.base u, ⟨u, rfl⟩, (Scheme.Hom.comp_apply a b u).symm⟩

theorem basicOpen_f : (X₀).basicOpen (f R₀ F j) = (ιMid R₀ F j).opensRange := by
  rw [f, ← Scheme.image_basicOpen, basicOpen_sF, image_opensRange]

theorem opensRange_ιMid' : (fInf R₀ F j ≫ ιInf R₀ F j).opensRange = (ιMid R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_opensRange]
  rw [← ιMid_eq']

theorem basicOpen_g : (X₀).basicOpen (g R₀ F j) = (ιMid R₀ F j).opensRange := by
  rw [g, ← Scheme.image_basicOpen, basicOpen_sI, image_opensRange, opensRange_ιMid']

theorem U_inf_V : U R₀ F j ⊓ V R₀ F j = (ιMid R₀ F j).opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨x₀, -, hx₀⟩, ⟨xi, -, hxi⟩⟩ := hx
    obtain ⟨u, rfl, rfl⟩ := (ιFin_eq_ιInf_iff R₀ F j x₀ xi).mp (hx₀.trans hxi.symm)
    exact ⟨u, hx₀⟩
  · rintro x ⟨u, rfl⟩
    refine ⟨⟨(fFin R₀ F j).base u, trivial, rfl⟩, ⟨(fInf R₀ F j).base u, trivial, ?_⟩⟩
    change (fInf R₀ F j ≫ ιInf R₀ F j).base u = (fFin R₀ F j ≫ ιFin R₀ F j).base u
    rw [glue_condition]

theorem presheaf_map_map_apply {Y : Scheme.{u}} {A B C : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(Y, A)) :
    Y.presheaf.map i' (Y.presheaf.map i t) = Y.presheaf.map i'' t := by
  rw [Subsingleton.elim i'' (i ≫ i'), Functor.map_comp, CommRingCat.comp_apply]

theorem presheaf_map_map_map_apply {Y : Scheme.{u}} {A B C D : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op C ⟶ op D) (k : op A ⟶ op D) (t : Γ(Y, A)) :
    Y.presheaf.map i'' (Y.presheaf.map i' (Y.presheaf.map i t)) = Y.presheaf.map k t := by
  rw [presheaf_map_map_apply i i' (i ≫ i'), presheaf_map_map_apply (i ≫ i') i'' k]

theorem app_res_f (W : (X₀).Opens) (hWU : W ≤ U R₀ F j) :
    (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R₀ F j)) =
      (XMid R₀ F j).presheaf.map (homOfLE le_top).op ((fFin R₀ F j).appTop (sF R₀ F j)) := by
  have step1 : (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R₀ F j)) =
      (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (ιMid R₀ F j).base).map (homOfLE hWU)).op
        ((ιMid R₀ F j).app (U R₀ F j) (f R₀ F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (ιMid R₀ F j).app (U R₀ F j) (f R₀ F j) =
      (fFin R₀ F j).app _ ((ιFin R₀ F j).app (U R₀ F j) (f R₀ F j)) := rfl
  have step4 : ∀ {V' : (XFin R₀ F j).Opens} (k : op ⊤ ⟶ op V'),
      (fFin R₀ F j).app V' ((XFin R₀ F j).presheaf.map k (sF R₀ F j)) =
        (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fFin R₀ F j).base).map k.unop).op
          ((fFin R₀ F j).appTop (sF R₀ F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, f, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_apply _ _ _ _

theorem app_res_g (W : (X₀).Opens) (hWV : W ≤ V R₀ F j) :
    (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R₀ F j)) =
      (XMid R₀ F j).presheaf.map (homOfLE le_top).op ((fInf R₀ F j).appTop (sI R₀ F j)) := by
  rw [Scheme.Hom.congr_app (ιMid_eq' R₀ F j) W, CommRingCat.comp_apply]
  have step1 : (fInf R₀ F j ≫ ιInf R₀ F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R₀ F j)) =
      (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R₀ F j ≫ ιInf R₀ F j).base).map (homOfLE hWV)).op
        ((fInf R₀ F j ≫ ιInf R₀ F j).app (V R₀ F j) (g R₀ F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (fInf R₀ F j ≫ ιInf R₀ F j).app (V R₀ F j) (g R₀ F j) =
      (fInf R₀ F j).app _ ((ιInf R₀ F j).app (V R₀ F j) (g R₀ F j)) := rfl
  have step4 : ∀ {V' : (XInf R₀ F j).Opens} (k : op ⊤ ⟶ op V'),
      (fInf R₀ F j).app V' ((XInf R₀ F j).presheaf.map k (sI R₀ F j)) =
        (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R₀ F j).base).map k.unop).op
          ((fInf R₀ F j).appTop (sI R₀ F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, g, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_map_apply _ _ _ _ _

omit [Fact (j ≠ 0)] in
theorem appTop_sF : (fFin R₀ F j).appTop (sF R₀ F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R₀ F j))).inv (inclFin R₀ F j (jChartFin R₀ F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclFin R₀ F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jChartFin R₀ F j)) h
  dsimp only at h'
  exact h'.symm

omit [Fact (j ≠ 0)] in
theorem appTop_sI : (fInf R₀ F j).appTop (sI R₀ F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R₀ F j))).inv (inclInf R₀ F j (jInvChartInf R₀ F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf R₀ F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jInvChartInf R₀ F j)) h
  dsimp only at h'
  exact h'.symm

theorem res_f_mul_res_g :
    ((X₀).presheaf.map (homOfLE (inf_le_left : U R₀ F j ⊓ V R₀ F j ≤ U R₀ F j)).op).hom (f R₀ F j) *
      ((X₀).presheaf.map (homOfLE (inf_le_right : U R₀ F j ⊓ V R₀ F j ≤ V R₀ F j)).op).hom (g R₀ F j) = 1 := by
  have hWle : U R₀ F j ⊓ V R₀ F j ≤ (ιMid R₀ F j).opensRange := (U_inf_V R₀ F j).le

  haveI : IsIso ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j)) := Scheme.Hom.isIso_app _ _ hWle
  have hinj : Function.Injective ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j)) :=
    (ConcreteCategory.bijective_of_isIso ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j))).1
  apply hinj
  rw [map_mul, map_one, app_res_f, app_res_g, appTop_sF, appTop_sI, ← map_mul, ← map_mul,
    inclFin_j_mul_inclInf_jInv, map_one, map_one]

end AlgebraicCurve.TwoChartIntegralModel.TwoChartsAux

namespace AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem chartFinOpen_le_image_top : chartFinOpen R F j ≤ (ιFin R F j) ''ᵁ ⊤ := (TwoChartsAux.U_eq R F j).ge

theorem chartInfOpen_le_image_top : chartInfOpen R F j ≤ (ιInf R F j) ''ᵁ ⊤ := (TwoChartsAux.V_eq R F j).ge

def jCoord : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, chartFinOpen R F j) :=
  ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE (chartFinOpen_le_image_top R F j)).op).hom
    (TwoChartsAux.f R F j)

def jInvCoord : Γ(AlgebraicCurve.TwoChartIntegralModel R F j, chartInfOpen R F j) :=
  ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE (chartInfOpen_le_image_top R F j)).op).hom
    (TwoChartsAux.g R F j)

theorem basicOpen_map_hom {Y : Scheme.{u}} {A B : Y.Opens} (i : op A ⟶ op B) (s : Γ(Y, A)) :
    Y.basicOpen ((Y.presheaf.map i).hom s) = B ⊓ Y.basicOpen s :=
  Y.basicOpen_res s i

theorem map_hom_map_hom {Y : Scheme.{u}} {A B C : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(Y, A)) :
    (Y.presheaf.map i').hom ((Y.presheaf.map i).hom t) = (Y.presheaf.map i'').hom t := by
  rw [Subsingleton.elim i'' (i ≫ i'), Functor.map_comp, CommRingCat.comp_apply]

theorem chartFinOpen_inf_chartInfOpen_eq_basicOpen_jCoord :
    chartFinOpen R F j ⊓ chartInfOpen R F j = (AlgebraicCurve.TwoChartIntegralModel R F j).basicOpen (jCoord R F j) := by
  rw [jCoord, basicOpen_map_hom, TwoChartsAux.basicOpen_f, ← TwoChartsAux.U_inf_V, TwoChartsAux.U_eq, TwoChartsAux.V_eq,
    ← inf_assoc, inf_idem]

theorem chartFinOpen_inf_chartInfOpen_eq_basicOpen_jInvCoord :
    chartFinOpen R F j ⊓ chartInfOpen R F j = (AlgebraicCurve.TwoChartIntegralModel R F j).basicOpen (jInvCoord R F j) := by
  rw [jInvCoord, basicOpen_map_hom, TwoChartsAux.basicOpen_g, ← TwoChartsAux.U_inf_V, TwoChartsAux.U_eq, TwoChartsAux.V_eq,
    inf_comm (chartInfOpen R F j) (chartFinOpen R F j ⊓ chartInfOpen R F j), inf_assoc, inf_idem]

theorem res_jCoord_mul_res_jInvCoord :
    ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map
        (homOfLE (inf_le_left : chartFinOpen R F j ⊓ chartInfOpen R F j ≤ chartFinOpen R F j)).op).hom (jCoord R F j) *
      ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map
        (homOfLE (inf_le_right : chartFinOpen R F j ⊓ chartInfOpen R F j ≤ chartInfOpen R F j)).op).hom (jInvCoord R F j) = 1 := by
  have hle : chartFinOpen R F j ⊓ chartInfOpen R F j ≤ TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j := by
    rw [TwoChartsAux.U_eq, TwoChartsAux.V_eq]
  rw [jCoord, jInvCoord,
    map_hom_map_hom _ _ ((homOfLE (inf_le_left : TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j ≤ TwoChartsAux.U R F j)).op ≫
      (homOfLE hle).op),
    map_hom_map_hom _ _ ((homOfLE (inf_le_right : TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j ≤ TwoChartsAux.V R F j)).op ≫
      (homOfLE hle).op),
    Functor.map_comp, Functor.map_comp, CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul,
    TwoChartsAux.res_f_mul_res_g, map_one]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

theorem isAffineHom_baseChangeι : IsAffineHom (baseChangeι R F j S) := by
  delta baseChangeι
  exact MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

abbrev chartFinOpenBC : (baseChange R F j S).Opens := baseChangeι R F j S ⁻¹ᵁ chartFinOpen R F j

abbrev chartInfOpenBC : (baseChange R F j S).Opens := baseChangeι R F j S ⁻¹ᵁ chartInfOpen R F j

def jCoordBC : Γ(baseChange R F j S, chartFinOpenBC R F j S) :=
  ((baseChangeι R F j S).app (chartFinOpen R F j)).hom (jCoord R F j)

def jInvCoordBC : Γ(baseChange R F j S, chartInfOpenBC R F j S) :=
  ((baseChangeι R F j S).app (chartInfOpen R F j)).hom (jInvCoord R F j)

def constSection (c : S) : Γ(baseChange R F j S, ⊤) :=
  ((baseChangeToBase R F j S).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv c)

theorem isAffineOpen_chartFinOpenBC : IsAffineOpen (chartFinOpenBC R F j S) :=
  haveI := isAffineHom_baseChangeι R F j S
  (isAffineOpen_chartFinOpen R F j).preimage _

theorem isAffineOpen_chartInfOpenBC : IsAffineOpen (chartInfOpenBC R F j S) :=
  haveI := isAffineHom_baseChangeι R F j S
  (isAffineOpen_chartInfOpen R F j).preimage _

theorem chartFinOpenBC_sup_chartInfOpenBC : chartFinOpenBC R F j S ⊔ chartInfOpenBC R F j S = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, twoChartCover]; rfl

theorem preimage_chartFinOpen_inf_chartInfOpen :
    baseChangeι R F j S ⁻¹ᵁ (chartFinOpen R F j ⊓ chartInfOpen R F j) = chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S := rfl

theorem chartFinOpenBC_inf_chartInfOpenBC_eq_basicOpen_jCoordBC :
    chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S = (baseChange R F j S).basicOpen (jCoordBC R F j S) := by
  rw [← preimage_chartFinOpen_inf_chartInfOpen, chartFinOpen_inf_chartInfOpen_eq_basicOpen_jCoord]
  exact Scheme.preimage_basicOpen _ _

theorem chartFinOpenBC_inf_chartInfOpenBC_eq_basicOpen_jInvCoordBC :
    chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S = (baseChange R F j S).basicOpen (jInvCoordBC R F j S) := by
  rw [← preimage_chartFinOpen_inf_chartInfOpen, chartFinOpen_inf_chartInfOpen_eq_basicOpen_jInvCoord]
  exact Scheme.preimage_basicOpen _ _

theorem res_jCoordBC_mul_res_jInvCoordBC :
    ((baseChange R F j S).presheaf.map
        (homOfLE (inf_le_left : chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S ≤ chartFinOpenBC R F j S)).op).hom
          (jCoordBC R F j S) *
      ((baseChange R F j S).presheaf.map
        (homOfLE (inf_le_right : chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S ≤ chartInfOpenBC R F j S)).op).hom
          (jInvCoordBC R F j S) = 1 := by
  have e : chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S ≤ baseChangeι R F j S ⁻¹ᵁ (chartFinOpen R F j ⊓ chartInfOpen R F j) :=
    le_of_eq (preimage_chartFinOpen_inf_chartInfOpen R F j S).symm
  have h1 : ((baseChange R F j S).presheaf.map
        (homOfLE (inf_le_left : chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S ≤ chartFinOpenBC R F j S)).op).hom
          (jCoordBC R F j S) =
      ((baseChangeι R F j S).appLE (chartFinOpen R F j ⊓ chartInfOpen R F j) _ e).hom
        (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map
          (homOfLE (inf_le_left : chartFinOpen R F j ⊓ chartInfOpen R F j ≤ chartFinOpen R F j)).op).hom (jCoord R F j)) := by
    rw [jCoordBC, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have h2 : ((baseChange R F j S).presheaf.map
        (homOfLE (inf_le_right : chartFinOpenBC R F j S ⊓ chartInfOpenBC R F j S ≤ chartInfOpenBC R F j S)).op).hom
          (jInvCoordBC R F j S) =
      ((baseChangeι R F j S).appLE (chartFinOpen R F j ⊓ chartInfOpen R F j) _ e).hom
        (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map
          (homOfLE (inf_le_right : chartFinOpen R F j ⊓ chartInfOpen R F j ≤ chartInfOpen R F j)).op).hom (jInvCoord R F j)) := by
    rw [jInvCoordBC, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  rw [h1, h2, ← map_mul, res_jCoord_mul_res_jInvCoord, map_one]

theorem constSection_sub (c₀ c₁ : S) :
    constSection R F j S c₀ - constSection R F j S c₁ = constSection R F j S (c₀ - c₁) := by
  rw [constSection, constSection, constSection, map_sub, map_sub]

theorem isUnit_constSection_sub {c₀ c₁ : S} (h : IsUnit (c₀ - c₁)) :
    IsUnit (constSection R F j S c₀ - constSection R F j S c₁) := by
  rw [constSection_sub]; exact (h.map _).map _

def jNeLocus (c : S) : (baseChange R F j S).Opens :=
  (baseChange R F j S).basicOpen
      (jCoordBC R F j S - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
        (constSection R F j S c)) ⊔
    (baseChange R F j S).basicOpen
      (1 - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartInfOpenBC R F j S ≤ ⊤)).op).hom
        (constSection R F j S c) * jInvCoordBC R F j S)

theorem jNeLocus_def (c : S) : jNeLocus R F j S c =
    (baseChange R F j S).basicOpen
      (jCoordBC R F j S - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartFinOpenBC R F j S ≤ ⊤)).op).hom
        (constSection R F j S c)) ⊔
    (baseChange R F j S).basicOpen
      (1 - ((baseChange R F j S).presheaf.map (homOfLE (le_top : chartInfOpenBC R F j S ≤ ⊤)).op).hom
        (constSection R F j S c) * jInvCoordBC R F j S) := rfl

end BaseChange

end AlgebraicCurve.TwoChartIntegralModel

end


