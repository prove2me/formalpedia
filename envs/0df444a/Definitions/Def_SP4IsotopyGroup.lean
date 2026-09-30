-- Prove2me | Definitions.Def_SP4IsotopyGroup
-- name    : SP4IsotopyGroup
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T03:55:31.839894+00:00
-- url     : https://prove2.me/theorems/a00d6e83-e8e1-450c-a425-2c4c4af8359b
-- title:
--   Group structure on smooth-isotopy classes
-- statement:
--   Let $M,N,P$ be real charted spaces with specified models with corners on real normed vector spaces. Smooth isotopy has the previously published meaning: a family of diffeomorphisms indexed by $[0,1]$, with jointly smooth forward evaluation and specified endpoints.
--
--   Pointwise composition of two such families gives an isotopy of the composite endpoints. An isotopy $F$ from $f$ to $g$ also supplies an isotopy of inverse endpoints through the explicit family
--
--   $$
--   t\longmapsto g^{-1}\circ F_{1-t}\circ f^{-1}.
--   $$
--
--   This construction uses fixed endpoint inverses; it does not require a new assumption that the pointwise inverse family $F_t^{-1}$ is jointly smooth. Smooth changes of coordinates preserve and reflect isotopy of self-diffeomorphisms.
--
--   Composition and inversion consequently descend to the existing quotient by smooth isotopy. The self-map quotient is a group, with
--
--   $$
--   [f][g]=[f\circ g],\qquad [f]^{-1}=[f^{-1}],\qquad 1=[\operatorname{id}_M].
--   $$
--
--   Equality of two classes is exactly existence of a smooth isotopy of their representatives; in particular the identity class consists exactly of self-diffeomorphisms isotopic to the identity.
--
--   No compactness, connectedness, finite-dimensionality, orientation or additional manifold-compatibility typeclass is assumed. This is the quotient by the stated smooth-family relation, not a separately proved identification with topological connected components of a diffeomorphism group. It does not prove disk isotopy extension, Cerf's theorem, collar/gluing invariance, the smooth embedding-orbit classification or SP4.
-- source:
--   Derived foundational extension of Ryan Shin, Isotopy.lean, definitions at lines 33–118 (SHA-256 5c3ef5532fc26dce842c963bf7bc2d902692f11ab112839e9afbb79e8273fee5), and the published SP4SmoothIsotopy interface. Motivated by smooth_orbit_framework.md, section The standard orbit and the optional domain quotient (SHA-256 f8f4cdaa5ec5670fc9201f319ab1d3fd1b7c43c0ed576c533233614dd0e36897). These newly derived composition/inverse/quotient constructions are not the geometric orbit-bijection theorem. The admitted Cerf statement is excluded.

import Definitions.Def_SP4SmoothIsotopy

/-! Composition and inversion on the actual smooth-isotopy quotient.

This extends the published definition without modifying its smoothness hypotheses.
The inverse isotopy is constructed using fixed endpoint inverses; it does not
assert joint smoothness of the pointwise inverse family.
-/

open scoped Manifold ContDiff

noncomputable section

namespace SP4Isotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

namespace Diffeotopy

/-- Pointwise composition of two jointly smooth families. -/
def comp {φ ψ : M ≃ₘ⟮I, I'⟯ M'} {f g : M' ≃ₘ⟮I', I''⟯ M''}
    (h : Diffeotopy φ ψ) (k : Diffeotopy f g) :
    Diffeotopy (φ.trans f) (ψ.trans g) where
  slice t := (h.slice t).trans (k.slice t)
  contMDiff := k.contMDiff.comp (contMDiff_fst.prodMk h.contMDiff)
  slice_bot := by rw [h.slice_bot, k.slice_bot]
  slice_top := by rw [h.slice_top, k.slice_top]

/-- An isotopy between inverses, with slice
`ψ⁻¹ ∘ h(1-t) ∘ φ⁻¹`. Only the fixed endpoint inverses are used. -/
def inverse {φ ψ : M ≃ₘ⟮I, I'⟯ M'} (h : Diffeotopy φ ψ) :
    Diffeotopy φ.symm ψ.symm := by
  have h' := ((Diffeotopy.refl φ.symm).comp h.symm).comp
    (Diffeotopy.refl ψ.symm)
  convert h' using 1 <;> ext x <;> simp

end Diffeotopy

namespace Isotopic

/-- Smooth isotopy is respected by composition of diffeomorphisms. -/
theorem comp {φ ψ : M ≃ₘ⟮I, I'⟯ M'} {f g : M' ≃ₘ⟮I', I''⟯ M''}
    (h : Isotopic φ ψ) (k : Isotopic f g) :
    Isotopic (φ.trans f) (ψ.trans g) := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  exact ⟨h.comp k⟩

/-- Smooth isotopy is respected by inversion of diffeomorphisms. -/
theorem inverse {φ ψ : M ≃ₘ⟮I, I'⟯ M'} (h : Isotopic φ ψ) :
    Isotopic φ.symm ψ.symm := by
  rcases h with ⟨h⟩
  exact ⟨h.inverse⟩

/-- Changing smooth coordinates preserves and reflects isotopy of self-maps. -/
theorem conjugate_iff (e : M ≃ₘ⟮I, I'⟯ M') (φ ψ : M ≃ₘ⟮I, I⟯ M) :
    Isotopic ((e.symm.trans φ).trans e) ((e.symm.trans ψ).trans e) ↔
      Isotopic φ ψ := by
  constructor
  · intro h
    have h' := (Isotopic.comp (Isotopic.comp ⟨Diffeotopy.refl e⟩ h)
      ⟨Diffeotopy.refl e.symm⟩)
    convert h' using 1 <;> ext x <;> simp
  · intro h
    exact (Isotopic.comp (Isotopic.comp ⟨Diffeotopy.refl e.symm⟩ h)
      ⟨Diffeotopy.refl e⟩)

end Isotopic

namespace IsotopyClasses

/-- The smooth-isotopy class of a diffeomorphism. -/
def mk (φ : M ≃ₘ⟮I, I'⟯ M') : IsotopyClasses I I' M M' :=
  Quotient.mk _ φ

/-- Composition descends to the quotient; the first arrow is applied first. -/
def comp (a : IsotopyClasses I I' M M') (b : IsotopyClasses I' I'' M' M'') :
    IsotopyClasses I I'' M M'' :=
  Quotient.liftOn₂ a b (fun φ f => mk (φ.trans f))
    (fun _ _ _ _ h k => Quotient.sound (h.comp k))

/-- Inversion descends to the quotient. -/
def inverse (a : IsotopyClasses I I' M M') : IsotopyClasses I' I M' M :=
  Quotient.liftOn a (fun φ => mk φ.symm)
    (fun _ _ h => Quotient.sound h.inverse)

@[simp]
theorem comp_mk (φ : M ≃ₘ⟮I, I'⟯ M') (f : M' ≃ₘ⟮I', I''⟯ M'') :
    comp (mk φ) (mk f) = mk (φ.trans f) := rfl

@[simp]
theorem inverse_mk (φ : M ≃ₘ⟮I, I'⟯ M') : inverse (mk φ) = mk φ.symm := rfl

/-- The group of smooth-isotopy classes of self-diffeomorphisms.
Multiplication follows function composition: `a * b` applies `b` first. -/
instance group : Group (IsotopyClasses I I M M) where
  mul a b := comp b a
  one := mk (Diffeomorph.refl I M ∞)
  inv := inverse
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ
    change mk (χ.trans (ψ.trans φ)) = mk ((χ.trans ψ).trans φ)
    rfl
  one_mul a := by
    refine Quotient.inductionOn a ?_
    intro φ
    change mk (φ.trans (Diffeomorph.refl I M ∞)) = mk φ
    simp
  mul_one a := by
    refine Quotient.inductionOn a ?_
    intro φ
    change mk ((Diffeomorph.refl I M ∞).trans φ) = mk φ
    simp
  inv_mul_cancel a := by
    refine Quotient.inductionOn a ?_
    intro φ
    change mk (φ.trans φ.symm) = mk (Diffeomorph.refl I M ∞)
    simp

@[simp]
theorem mk_mul (φ ψ : M ≃ₘ⟮I, I⟯ M) : mk φ * mk ψ = mk (ψ.trans φ) := rfl

@[simp]
theorem mk_inv (φ : M ≃ₘ⟮I, I⟯ M) : (mk φ)⁻¹ = mk φ.symm := rfl

/-- Equality in the quotient is exactly existence of a jointly smooth isotopy. -/
theorem mk_eq_mk_iff (φ ψ : M ≃ₘ⟮I, I'⟯ M') :
    mk φ = mk ψ ↔ Isotopic φ ψ := Quotient.eq

/-- The identity class consists exactly of self-diffeomorphisms isotopic to the identity. -/
theorem mk_eq_one_iff (φ : M ≃ₘ⟮I, I⟯ M) :
    mk φ = 1 ↔ Isotopic φ (Diffeomorph.refl I M ∞) := Quotient.eq

end IsotopyClasses

end SP4Isotopy


