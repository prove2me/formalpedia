-- Prove2me | Definitions.Def_AlgebraicCurve_UniversalDivisor
-- name    : AlgebraicCurve_UniversalDivisor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2001d8fa-7491-5078-8b1e-ab52c801e677
-- title:
--   Relative effective divisors on a curve and a universal divisor
-- statement:
--   Fix a field $k$, a $k$-scheme $c : C \to \operatorname{Spec} k$ and $r \in \mathbb{N}$. For a $k$-scheme $t : T \to \operatorname{Spec} k$, the structure `RelEffDivisor C c r T t` packages a quasi-coherent ideal sheaf on the fibre product $C \times_k T$ (in Mathlib's presentation, an element of `(pullback c t).IdealSheafData`) together with three conditions on the composite of the closed immersion of the associated closed subscheme with the second projection $C \times_k T \to T$: this morphism is finite, it is flat, and its flat rank at every point $s$ of $T$ equals $r$. Two such divisors are equal as soon as their ideal sheaf data agree, so the remaining fields are proof-irrelevant conditions on the chosen ideal sheaf datum. For a $k$-morphism $\varphi : T \to C_{\mathrm{sym}}$, `mapOnProd` is the induced morphism $1_C \times \varphi : C \times_k T \to C \times_k C_{\mathrm{sym}}$; `isPullback_mapOnProd` records that it makes $C \times_k T$ the fibre product of $C \times_k C_{\mathrm{sym}}$ and $T$ over $C_{\mathrm{sym}}$. The predicate `PullsBack Dcan φ hφ D'` asserts the literal equality of ideal sheaf data $(1_C \times \varphi)^{*} I_{D_{\mathrm{can}}} = I_{D'}$, and `RelEffDivisor.pullbackAlong` constructs the divisor with that ideal sheaf, finiteness, flatness and constant rank $r$ being inherited by base change along the resulting pullback squares; `pullbackAlong_comp` gives compatibility with composition of morphisms, and `PullsBack.eq_pullbackAlong`, `PullsBack.isPullback` identify a divisor satisfying the predicate with this construction and exhibit the corresponding cartesian square of subschemes.
--
--   Finally, `UnivDivisorPack C c r Csym csym` is a structure carrying a divisor $D_{\mathrm{can}}$ of degree $r$ on $C \times_k C_{\mathrm{sym}}$ over $C_{\mathrm{sym}}$ together with two theorems as fields: over every integral $k$-scheme $T$ that is locally of finite type and quasi-compact over $k$, every degree-$r$ relative effective divisor on $C \times_k T$ is $(1_C \times \varphi)^{*} D_{\mathrm{can}}$ for some $k$-morphism $\varphi : T \to C_{\mathrm{sym}}$; and over every reduced such $T$, any two $k$-morphisms pulling $D_{\mathrm{can}}$ back to the same divisor coincide. Thus representability is asserted only in the weakened form of existence over integral test schemes and uniqueness over reduced ones, with no condition imposed over non-reduced bases.
--
--   **Relation to Mathlib.** Mathlib has no notion of relative effective divisor or of a universal such divisor; these are the project's own, stated on top of Mathlib's `Scheme.IdealSheafData` with its `comap` and associated closed subscheme, the morphism properties `IsFinite` and `Flat`, and the flat rank `Scheme.Hom.finrank`.
--
--   **Where it is used.** The intended instances are the symmetric powers $C^{(r)}$ of a curve carrying the incidence divisor, with $r = 0$ giving $\operatorname{Spec} k$ and $r = 1$ the diagonal on $C \times_k C$; this is the divisor-theoretic groundwork for Jacobians of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_UniversalDivisor.lean

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]

structure RelEffDivisor (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) where
  I : (pullback c t).IdealSheafData
  isFinite : IsFinite (I.subschemeι ≫ pullback.snd c t)
  flat : Flat (I.subschemeι ≫ pullback.snd c t)
  finrank_eq : ∀ s : T, (I.subschemeι ≫ pullback.snd c t).finrank s = r

@[ext] lemma RelEffDivisor.ext {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {D₁ D₂ : RelEffDivisor C c r T t}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

noncomputable def mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    pullback c t ⟶ pullback c csym :=
  pullback.map c t c csym (𝟙 C) φ (𝟙 (Spec (CommRingCat.of k))) (by simp)
    (by rw [Category.comp_id, hφ])

@[reassoc (attr := simp)]
lemma mapOnProd_fst {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.fst c csym = pullback.fst c t := by
  simp only [mapOnProd, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma mapOnProd_snd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.snd c csym = pullback.snd c t ≫ φ := by
  simp only [mapOnProd, pullback.map, pullback.lift_snd]

lemma isPullback_mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    IsPullback (mapOnProd c φ hφ) (pullback.snd c t) (pullback.snd c csym) φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst c csym) (v₁₃ := c) (h₂₂ := csym) ?_
    (mapOnProd_snd c φ rfl) (IsPullback.of_hasPullback c csym)
  simpa using IsPullback.of_hasPullback c (φ ≫ csym)

def PullsBack {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) (D' : RelEffDivisor C c r T t) : Prop :=
  Dcan.I.comap (mapOnProd c φ hφ) = D'.I

section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

noncomputable def comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : (I.comap (mapOnProd c φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProd c φ hφ)).hom ≫ pullback.snd _ _

lemma isPullback_comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ) (I.comap (mapOnProd c φ hφ)).subschemeι
      I.subschemeι (mapOnProd c φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProd c φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMap]
  · simp
  · simp [comapSubschemeMap]

lemma isPullback_comap_snd (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ)
      ((I.comap (mapOnProd c φ hφ)).subschemeι ≫ pullback.snd c t)
      (I.subschemeι ≫ pullback.snd c csym) φ :=
  (isPullback_comapSubschemeMap I φ hφ).paste_vert (isPullback_mapOnProd c φ hφ)

end transport

noncomputable def RelEffDivisor.pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : RelEffDivisor C c r T t where
  I := Dcan.I.comap (mapOnProd c φ hφ)
  isFinite :=
    have := Dcan.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  flat :=
    have := Dcan.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  finrank_eq s := by
    have := Dcan.isFinite
    have := Dcan.flat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd Dcan.I φ hφ) s]
    exact Dcan.finrank_eq (φ s)

theorem pullsBack_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    PullsBack Dcan φ hφ (Dcan.pullbackAlong φ hφ) := rfl

lemma PullsBack.eq_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    D' = Dcan.pullbackAlong φ hφ :=
  RelEffDivisor.ext h.symm

lemma PullsBack.isPullback {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ Dcan.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd c t)
        (Dcan.I.subschemeι ≫ pullback.snd c csym) φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd Dcan.I φ hφ⟩

lemma RelEffDivisor.pullbackAlong_comp {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t)
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (φ' : T' ⟶ T)
    (hφ' : φ' ≫ t = t') :
    (Dcan.pullbackAlong φ hφ).pullbackAlong φ' hφ' =
      Dcan.pullbackAlong (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) := by
  refine RelEffDivisor.ext ?_
  change (Dcan.I.comap _).comap _ = Dcan.I.comap _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  ext <;> simp

structure UnivDivisorPack (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (Csym : Scheme.{u}) (csym : Csym ⟶ Spec (CommRingCat.of k)) where
  Dcan : RelEffDivisor C c r Csym csym
  exists_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsIntegral T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t),
    ∃ (φ : T ⟶ Csym) (hφ : φ ≫ csym = t), PullsBack Dcan φ hφ D'
  eq_of_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsReduced T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t)
    (φ₁ φ₂ : T ⟶ Csym) (hφ₁ : φ₁ ≫ csym = t) (hφ₂ : φ₂ ≫ csym = t),
    PullsBack Dcan φ₁ hφ₁ D' → PullsBack Dcan φ₂ hφ₂ D' → φ₁ = φ₂

end AlgebraicCurve


