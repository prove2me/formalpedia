-- Prove2me | Definitions.Def_RPLib_S4_EtShChartSch
-- name    : RPLib_S4_EtShChartSch
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:46:18.221735+00:00
-- url     : https://prove2.me/theorems/e042ed1f-3de3-423b-9777-135e3a1cd034
-- title:
--   Charts for lisse etale sheaves on $\mathrm{Spec}\,A$
-- statement:
--   Let $A$ be a noetherian integrally closed domain and $G$ a lisse etale sheaf of $\Lambda$-modules on $\mathrm{Spec}\,A$. Then every point $u$ of every etale $U \to \mathrm{Spec}\,A$ has an etale neighbourhood $T \to \mathrm{Spec}\,A$ mapping to $U$ on which $G$ is constant and which has at most one point over the generic point of $\mathrm{Spec}\,A$ (take a trivialisation at the image of $u$, an affine open of the fibre product and the localisation given by the algebraic chart lemma).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_EtShFullAbs
import Definitions.Def_RPLib_S4_EtShChartAlg
import Definitions.Def_RPLib_S4_EtShGenBr

/-!
# S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`

Let `A` be a noetherian integrally closed domain and `G` a lisse etale sheaf on `Spec A`. Then `G` has charts at the
generic point (`hChart`): every point `u` of every etale `U → Spec A` has an etale neighbourhood `T → Spec A` over `U`
on which `G` is constant and which has at most one point over the generic point.

Proof: take a trivialising `U₁ → Spec A` for `G` at the image of `u`, a point `p` of `U ×_{Spec A} U₁` over `u`, an
affine open `Spec R ⊆ U ×_{Spec A} U₁` around `p` (`R` is etale over `A`), and the localisation
`Spec (R_{f₀})_{f₁} ⊆ Spec R` of `ChartAlg.exists_chartAlg` (`chart_of` assembles the chart).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace ChartSch

section Abstract

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X) {G : EtSh Λ X}

/-- **Assembling a chart**: an etale `ι : T ⟶ U ×_X U₁` with `G|_{U₁}` constant, a point of `T` over `u` and at most
one point of `T` over `x0` give a chart of `G` at `u`. -/
theorem chart_of {U U₁ : X.Etale} (u : U.left) {T : Scheme.{u}} (ι : T ⟶ pullback U.hom U₁.hom) [Etale ι]
    (M : ModuleCat.{u} Λ) (e : (pull U₁.hom Λ).obj G ≅ constSh Λ U₁.left M) (w : T)
    (hw : pullback.fst U.hom U₁.hom (ι w) = u)
    (huniq : ∀ w₁ w₂ : T, U₁.hom (pullback.snd U.hom U₁.hom (ι w₁)) = x0 →
      U₁.hom (pullback.snd U.hom U₁.hom (ι w₂)) = x0 → w₁ = w₂) :
    ∃ (T : Scheme.{u}) (h : T ⟶ X) (_ : Etale h)
      (g : (etComp h).obj (etId T) ⟶ U) (w : ((etComp h).obj (etId T)).left), g.left w = u ∧
      (∃ M : ModuleCat.{u} Λ, Nonempty ((pull h Λ).obj G ≅ constSh Λ T M)) ∧
      ∀ w₁ w₂ : T, h w₁ = x0 → h w₂ = x0 → w₁ = w₂ := by
  have : Etale U.hom := U.prop
  have : Etale U₁.hom := U₁.prop
  refine ⟨T, (ι ≫ pullback.snd U.hom U₁.hom) ≫ U₁.hom, inferInstance,
    MorphismProperty.Over.homMk (ι ≫ pullback.fst U.hom U₁.hom) ?_ trivial, w, ?_,
    ⟨M, ⟨(pullCompIso Λ (ι ≫ pullback.snd U.hom U₁.hom) U₁.hom).app G ≪≫
      (pull (ι ≫ pullback.snd U.hom U₁.hom) Λ).mapIso e ≪≫
      pullConst Λ (ι ≫ pullback.snd U.hom U₁.hom) M⟩⟩, ?_⟩
  · show (ι ≫ pullback.fst U.hom U₁.hom) ≫ U.hom = 𝟙 T ≫ ((ι ≫ pullback.snd U.hom U₁.hom) ≫ U₁.hom)
    simp only [Category.id_comp, Category.assoc, pullback.condition]
  · show (ι ≫ pullback.fst U.hom U₁.hom) w = u
    rw [Scheme.Hom.comp_apply]
    exact hw
  · intro w₁ w₂ h₁ h₂
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₁ h₂
    exact huniq w₁ w₂ h₁ h₂

end Abstract

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- **Lisse sheaves on `Spec A` have charts at the generic point.** -/
theorem hChart (G : EtSh Λ (Spec (CommRingCat.of A))) (hG : IsLisse Λ G) :
    FullAbs.HChart (GenBr.genPt A) G := by
  intro U u
  have : Etale U.hom := U.prop
  obtain ⟨U₁, v₁, hv₁, M, -, ⟨e⟩⟩ := hG (U.hom u)
  have : Etale U₁.hom := U₁.prop
  obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := U₁.hom) u v₁ hv₁.symm
  let 𝒱 := (pullback U.hom U₁.hom).affineOpenCover
  obtain ⟨q, hq⟩ := 𝒱.covers p
  let b1 := 𝒱.f (𝒱.idx p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (b1 ≫ pullback.snd U.hom U₁.hom ≫ U₁.hom)
  let _ : Algebra A (𝒱.X (𝒱.idx p)) := ψ.hom.toAlgebra
  have hEt : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Algebra.Etale A (𝒱.X (𝒱.idx p)) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt)
  have hqP : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨f₀, f₁, P₀, hP₀, huniq⟩ := ChartAlg.exists_chartAlg (A := A) (R := 𝒱.X (𝒱.idx p)) q.asIdeal
  have hin : Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) P₀) = q :=
    PrimeSpectrum.ext hP₀
  have key : ∀ w : Spec (CommRingCat.of (Localization.Away f₁)),
      U₁.hom (pullback.snd U.hom U₁.hom (b1
        (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) w)))) =
      Spec.map ψ (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) w)) := by
    intro w
    rw [hψ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  refine ChartSch.chart_of (GenBr.genPt A) u
    (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀))) ≫ b1) M e P₀ ?_ ?_
  · have h1 : pullback.fst U.hom U₁.hom (b1
        (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) P₀))) = u :=
      ((congrArg (pullback.fst U.hom U₁.hom) (congrArg b1 hin)).trans
        (congrArg (pullback.fst U.hom U₁.hom) hq)).trans hp₁
    exact h1
  · intro w₁ w₂ h₁ h₂
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₁ h₂
    have e₁ := congrArg PrimeSpectrum.asIdeal ((key w₁).symm.trans h₁)
    have e₂ := congrArg PrimeSpectrum.asIdeal ((key w₂).symm.trans h₂)
    exact huniq w₁ w₂ e₁ e₂

end Spec

end ChartSch

end RamanujanPetersson.EtSheaves


