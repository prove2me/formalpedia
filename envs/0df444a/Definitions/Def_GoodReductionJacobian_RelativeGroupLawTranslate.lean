-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
-- name    : GoodReductionJacobian_RelativeGroupLawTranslate
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/b1c5d1af-e9ba-5236-98b8-12076b316785
-- title:
--   Right translation, translation and stabiliser for relative group laws
-- statement:
--   Throughout, $R$ is a commutative ring and $f : A \to \operatorname{Spec} R$ a scheme over $\operatorname{Spec} R$ equipped with a `RelativeGroupLaw` $L$, i.e. a group structure on each set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over a variable $R$-scheme $t : T \to \operatorname{Spec} R$, natural in $T$.
--
--   First, for a morphism $q : X \to T$ of schemes and two sheaves of modules $M, M'$ on $X$, `Scheme.Modules.LocallyIsoOver q M M'` asserts that every point $\tau$ of $T$ lies in an open $U \subseteq T$ for which the pullbacks of $M$ and of $M'$ along the inclusion of the open subscheme $q^{-1}U$ are isomorphic (merely `Nonempty`, so an existence statement about isomorphisms, not a chosen one). It is shown to be reflexive, symmetric and transitive, a global isomorphism yields it, and `LocallyIsoOver.restrict` produces from a trivialisation over $U$ one over any smaller open $V \le U$, using the standard coherence isomorphisms for pullbacks of sheaves of modules.
--
--   Second, over a test scheme $t : T \to \operatorname{Spec} R$, on the fibre product $A \times_{\operatorname{Spec} R} T$ two points over $\mathrm{pr}_T$ followed by $t$ are singled out: `fstPoint`, the first projection, and `sndPoint` of $x$, namely $\mathrm{pr}_T$ followed by $x$. Their product under $L$ has underlying morphism `mulRight t x` : $A \times_R T \to A$, the right translation $(a,\tau) \mapsto a \cdot x(\tau)$; `mulRight_over` records that it lies over $\mathrm{pr}_T$ followed by $t$, and `mulRight_one` that for the unit point it is $\mathrm{pr}_A$. For an $R$-point $x$ (a point over the identity of $\operatorname{Spec} R$), `translate x` : $A \to A$ is the underlying morphism of the product of the identity point of $A(A)$ with $f$ followed by $x$; it lies over $f$, and the translation by the unit point is the identity.
--
--   Finally, `IsInStabilizer L 𝓛 t x`, for a sheaf of modules $\mathcal L$ on $A$, says that the pullback of $\mathcal L$ along `mulRight t x` and the pullback of $\mathcal L$ along $\mathrm{pr}_A$ are `LocallyIsoOver` the projection $\mathrm{pr}_T$ — that is, $T^*_x \mathcal L_T \cong \mathcal L_T$ locally on $T$. Two instances are proved: the unit point stabilises every $\mathcal L$, and every point stabilises the unit sheaf of modules of $A$.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients (`Scheme.Modules`, pullback of sheaves of modules with its coherence isomorphisms, `SheafOfModules.unit`) but not the notions defined here: the functorial relative group law, right translation and translation morphisms attached to it, the relation 'locally isomorphic over the base', and the stabiliser predicate are the project's own.
--
--   **Where it is used.** These definitions belong to the project's Néron-model and relative Picard vocabulary, where the stabiliser sub-functor $T \mapsto \{x \in A(T) : x \text{ stabilises } \mathcal L\}$ and the relation 'isomorphic locally over the base' are the input for the study of line bundles on Jacobians and their good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawTranslate.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

def LocallyIsoOver (q : X ⟶ T) (M M' : X.Modules) : Prop :=
  ∀ τ : T, ∃ U : T.Opens, τ ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M')

namespace LocallyIsoOver

variable {q : X ⟶ T} {M M' M'' : X.Modules}

theorem of_iso (q : X ⟶ T) {M M' : X.Modules} (e : M ≅ M') : LocallyIsoOver q M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem rfl : LocallyIsoOver q M M := of_iso q (Iso.refl M)

theorem symm (h : LocallyIsoOver q M M') : LocallyIsoOver q M' M := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  exact ⟨U, hτ, ⟨e.symm⟩⟩

def restrict {U V : T.Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') :
    (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj M' :=
  have hle : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (q ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

theorem trans (h : LocallyIsoOver q M M') (h' : LocallyIsoOver q M' M'') : LocallyIsoOver q M M'' := fun τ => by
  obtain ⟨U, hτ, ⟨e⟩⟩ := h τ
  obtain ⟨U', hτ', ⟨e'⟩⟩ := h' τ
  exact ⟨U ⊓ U', ⟨hτ, hτ'⟩, ⟨restrict inf_le_left e ≪≫ restrict inf_le_right e'⟩⟩

end LocallyIsoOver

end AlgebraicGeometry.Scheme.Modules

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def fstPoint (_L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver (pullback.snd f t ≫ t) f :=
  ⟨pullback.fst f t, pullback.condition⟩

def sndPoint (_L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : SchemeHomOver (pullback.snd f t ≫ t) f :=
  ⟨pullback.snd f t ≫ x.1, by rw [Category.assoc, x.2]⟩

@[simp] theorem fstPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.fstPoint t).1 = pullback.fst f t := rfl

@[simp] theorem sndPoint_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : (L.sndPoint t x).1 = pullback.snd f t ≫ x.1 := rfl

def mulRight (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : pullback f t ⟶ A :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).1

theorem mulRight_over (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.mulRight t x ≫ f = pullback.snd f t ≫ t :=
  (L.mul (pullback.snd f t ≫ t) (L.fstPoint t) (L.sndPoint t x)).2

theorem sndPoint_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.sndPoint t (L.one t) = L.one (pullback.snd f t ≫ t) := by
  have h := L.one_natural t (pullback.snd f t ≫ t) (pullback.snd f t) rfl
  rw [← h]
  rfl

theorem mulRight_one (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    L.mulRight t (L.one t) = pullback.fst f t := by
  unfold mulRight
  rw [sndPoint_one, L.mul_one]
  rfl

def translate (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : A ⟶ A :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).1

theorem translate_over (L : RelativeGroupLaw R f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate x ≫ f = f :=
  (L.mul f idPoint ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩).2

theorem translate_one (L : RelativeGroupLaw R f) : L.translate (L.one (𝟙 (Spec (CommRingCat.of R)))) = 𝟙 A := by
  have h : (⟨f ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1, by
      rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]⟩ : SchemeHomOver f f) =
      L.one f := by
    have h1 := L.one_natural (𝟙 (Spec (CommRingCat.of R))) f f (Category.comp_id f)
    rw [← h1]
    rfl
  unfold translate
  rw [h, L.mul_one]

def IsInStabilizer (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : Prop :=
  Scheme.Modules.LocallyIsoOver (pullback.snd f t)
    ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)

theorem isInStabilizer_one (L : RelativeGroupLaw R f) (𝓛 : A.Modules) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : L.IsInStabilizer 𝓛 t (L.one t) := by
  unfold IsInStabilizer
  rw [mulRight_one]
  exact Scheme.Modules.LocallyIsoOver.rfl

theorem isInStabilizer_unit (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : L.IsInStabilizer (SheafOfModules.unit A.ringCatSheaf) t x := by
  exact Scheme.Modules.LocallyIsoOver.of_iso _
    (Scheme.Modules.pullbackUnitIso (L.mulRight t x) ≪≫ (Scheme.Modules.pullbackUnitIso (pullback.fst f t)).symm)

end GoodReductionJacobian.RelativeGroupLaw

end


