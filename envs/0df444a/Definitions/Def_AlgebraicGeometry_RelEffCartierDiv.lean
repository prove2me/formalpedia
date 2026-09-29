-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
-- name    : AlgebraicGeometry_RelEffCartierDiv
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/00d88bf5-6be2-5dbe-a754-a49b92d6720b
-- title:
--   Relative effective divisors on a fibre product of schemes
-- statement:
--   Fix a morphism of schemes $f\colon\mathcal C\to S$, a natural number $r$, and an $S$-scheme $g\colon T\to S$. The structure `RelEffCartierDiv f r g` consists of a quasi-coherent ideal sheaf $\mathcal I$ on the fibre product $\mathcal C\times_S T$ (a term of Mathlib's `IdealSheafData` on `pullback f g`), together with four conditions on the composite $D=V(\mathcal I)\hookrightarrow \mathcal C\times_S T\to T$ of the closed immersion `I.subschemeι` with the second projection: that it is finite, flat and locally of finite presentation, and that its `finrank` at every point $t\in T$ equals $r$. Thus a term is the datum of a closed subscheme of $\mathcal C_T$ which is finite locally free of rank $r$ over $T$; no invertibility of $\mathcal I$, and no smoothness or properness of $f$, is imposed. Two such divisors are equal as soon as their ideal sheaves agree.
--
--   For an $S$-morphism $\varphi\colon T\to T'$ (given by $\varphi$ together with a proof that $\varphi$ followed by $g'$ is $g$), `mapOnProdOver` is the induced morphism $\mathcal C\times_S T\to\mathcal C\times_S T'$ obtained from the identity on $\mathcal C$ and $\varphi$; its compatibilities with the two projections are recorded, as is the fact that it sits in a cartesian square over $\varphi$ with the projections to $T$ and $T'$. Consequently `RelEffCartierDiv.pullbackAlong` takes a divisor $D$ over $T'$ to the divisor over $T$ whose ideal sheaf is the inverse image `D.I.comap` along `mapOnProdOver`; finiteness, flatness, local finite presentation and the rank $r$ are transported along the resulting cartesian square (`isPullback_comap_snd_over`, together with `comapSubschemeMapOver` identifying the comap subscheme as a fibre product). The predicate `PullsBackOver D φ hφ D'` asserts the equality of ideal sheaves `D.I.comap (mapOnProdOver f φ hφ) = D'.I`; it holds for `pullbackAlong`, characterises $D'$ up to equality, and yields a cartesian square comparing $V(D'.\mathcal I)\to T$ with $V(D.\mathcal I)\to T'$. Functoriality is recorded: `pullbackAlong` along an identity is the identity, and along a composite $\varphi'$ followed by $\varphi$ it is the composite of the two pullbacks.
--
--   Finally, when $S=\operatorname{Spec} k$ for a field $k$, `toRelEffDivisor` forgets the local finite presentation field to give the field-level structure [`AlgebraicCurve.RelEffDivisor`](../def/AlgebraicCurve_UniversalDivisor.html#L19), `ofRelEffDivisor` reinstates it from a supplied proof, the first map is injective and is compatible with pullback along $S$-morphisms.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.IdealSheafData` (with `comap`, `subscheme`, `subschemeι`, `comapIso`), the morphism classes `IsFinite`, `Flat`, `LocallyOfFinitePresentation`, and `Scheme.Hom.finrank`; Mathlib has no structure for relative effective divisors, so this is the project's own notion. It is the version over an arbitrary base $S$ of the project's field-level [`AlgebraicCurve.RelEffDivisor`](../def/AlgebraicCurve_UniversalDivisor.html#L19), with the extra requirement that the divisor be locally of finite presentation over the base scheme.
--
--   **Where it is used.** These relative divisors are the $T$-points of the functor of finite locally free degree-$r$ closed subschemes of $\mathcal C_T$, the input to the relative Picard functor and to universal-divisor (symmetric power) constructions for a curve $\mathcal C\to S$ over a base such as $\operatorname{Spec}\mathbb Z_{(\ell)}$, as needed for modular curves and their Jacobians over non-field bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDiv.lean

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicCurve_UniversalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

structure RelEffCartierDiv {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)
    {T : Scheme.{u}} (g : T ⟶ S) where

  I : (pullback f g).IdealSheafData

  isFinite : IsFinite (I.subschemeι ≫ pullback.snd f g)

  flat : Flat (I.subschemeι ≫ pullback.snd f g)

  locallyOfFinitePresentation : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f g)

  finrank_eq : ∀ t : T, (I.subschemeι ≫ pullback.snd f g).finrank t = r

@[ext] lemma RelEffCartierDiv.ext {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} {D₁ D₂ : RelEffCartierDiv f r g}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

noncomputable def mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    pullback f g ⟶ pullback f g' :=
  pullback.map f g f g' (𝟙 𝒞) φ (𝟙 S) (by simp) (by rw [Category.comp_id, hφ])

@[reassoc (attr := simp)]
lemma mapOnProdOver_fst {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.fst f g' = pullback.fst f g := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma mapOnProdOver_snd {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    mapOnProdOver f φ hφ ≫ pullback.snd f g' = pullback.snd f g ≫ φ := by
  simp only [mapOnProdOver, pullback.map, pullback.lift_snd]

@[simp] lemma mapOnProdOver_id {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S} :
    mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 (pullback f g) := by
  ext <;> simp

lemma isPullback_mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    IsPullback (mapOnProdOver f φ hφ) (pullback.snd f g) (pullback.snd f g') φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_
    (mapOnProdOver_snd f φ rfl) (IsPullback.of_hasPullback f g')
  simpa using IsPullback.of_hasPullback f (φ ≫ g')

def PullsBackOver {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g)
    (D' : RelEffCartierDiv f r g) : Prop :=
  D.I.comap (mapOnProdOver f φ hφ) = D'.I

section transport

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

noncomputable def comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (I.comap (mapOnProdOver f φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProdOver f φ hφ)).hom ≫ pullback.snd _ _

lemma isPullback_comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ) (I.comap (mapOnProdOver f φ hφ)).subschemeι
      I.subschemeι (mapOnProdOver f φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProdOver f φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMapOver]
  · simp
  · simp [comapSubschemeMapOver]

lemma isPullback_comap_snd_over (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    IsPullback (comapSubschemeMapOver I φ hφ)
      ((I.comap (mapOnProdOver f φ hφ)).subschemeι ≫ pullback.snd f g)
      (I.subschemeι ≫ pullback.snd f g') φ :=
  (isPullback_comapSubschemeMapOver I φ hφ).paste_vert (isPullback_mapOnProdOver f φ hφ)

end transport

noncomputable def RelEffCartierDiv.pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) : RelEffCartierDiv f r g where
  I := D.I.comap (mapOnProdOver f φ hφ)
  isFinite :=
    have := D.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  flat :=
    have := D.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  locallyOfFinitePresentation :=
    have := D.locallyOfFinitePresentation
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  finrank_eq t := by
    have := D.isFinite
    have := D.flat
    have := D.locallyOfFinitePresentation
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd_over D.I φ hφ) t]
    exact D.finrank_eq (φ t)

theorem pullsBackOver_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    PullsBackOver D φ hφ (D.pullbackAlong φ hφ) := rfl

lemma PullsBackOver.eq_pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    D' = D.pullbackAlong φ hφ :=
  RelEffCartierDiv.ext h.symm

lemma PullsBackOver.isPullback {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} {D : RelEffCartierDiv f r g'}
    {T : Scheme.{u}} {g : T ⟶ S} {φ : T ⟶ T'} {hφ : φ ≫ g' = g}
    {D' : RelEffCartierDiv f r g} (h : PullsBackOver D φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ D.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd f g) (D.I.subschemeι ≫ pullback.snd f g') φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd_over D.I φ hφ⟩

lemma RelEffCartierDiv.pullbackAlong_comp {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T'' : Scheme.{u}} {g'' : T'' ⟶ S} (D : RelEffCartierDiv f r g'')
    {T' : Scheme.{u}} {g' : T' ⟶ S} (φ : T' ⟶ T'') (hφ : φ ≫ g'' = g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ' : T ⟶ T') (hφ' : φ' ≫ g' = g) :
    (D.pullbackAlong φ hφ).pullbackAlong φ' hφ' =
      D.pullbackAlong (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) := by
  refine RelEffCartierDiv.ext ?_
  change (D.I.comap _).comap _ = D.I.comap _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  ext <;> simp

lemma RelEffCartierDiv.pullbackAlong_id {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.pullbackAlong (𝟙 T) (Category.id_comp g) = D := by
  refine RelEffCartierDiv.ext ?_
  change D.I.comap (mapOnProdOver f (𝟙 T) (Category.id_comp g)) = D.I
  rw [show mapOnProdOver f (𝟙 T) (Category.id_comp g) = 𝟙 _ from mapOnProdOver_id f,
    Scheme.IdealSheafData.comap_id]

section FieldComparison

variable {k : Type u} [Field k]

def RelEffCartierDiv.toRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    AlgebraicCurve.RelEffDivisor C c r T t :=
  ⟨D.I, D.isFinite, D.flat, D.finrank_eq⟩

@[simp] lemma RelEffCartierDiv.toRelEffDivisor_I {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    D.toRelEffDivisor.I = D.I := rfl

lemma RelEffCartierDiv.toRelEffDivisor_injective {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (RelEffCartierDiv.toRelEffDivisor (c := c) (r := r) (t := t)) :=
  fun _ _ h => RelEffCartierDiv.ext (congrArg AlgebraicCurve.RelEffDivisor.I h)

def RelEffCartierDiv.ofRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    RelEffCartierDiv c r t :=
  ⟨D.I, D.isFinite, D.flat, h, D.finrank_eq⟩

@[simp] lemma RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    (RelEffCartierDiv.ofRelEffDivisor D h).toRelEffDivisor = D := rfl

lemma RelEffCartierDiv.toRelEffDivisor_pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ T') (hφ : φ ≫ t' = t) :
    (D.pullbackAlong φ hφ).toRelEffDivisor = D.toRelEffDivisor.pullbackAlong φ hφ := by
  refine AlgebraicCurve.RelEffDivisor.ext ?_
  change D.I.comap (mapOnProdOver c φ hφ) = D.I.comap (AlgebraicCurve.mapOnProd c φ hφ)
  congr 1

end FieldComparison

end AlgebraicGeometry


