-- Prove2me | Definitions.Def_SP4SmoothIsotopy
-- name    : SP4SmoothIsotopy
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T01:56:59.731719+00:00
-- url     : https://prove2.me/theorems/742a9098-e2af-462e-ba06-450ee0477446
-- title:
--   Smooth isotopies of diffeomorphisms and isotopy classes
-- statement:
--   Let $E,E'$ be real normed vector spaces, let $I,I'$ be models with corners on topological model domains $H,H'$, and let $M,N$ be topological spaces with the corresponding charted-space structures. For diffeomorphisms $f,g:M\to N$, a smooth isotopy consists of diffeomorphisms $F_t:M\to N$ indexed by $t\in[0,1]$, with jointly smooth forward evaluation and specified endpoints:
--
--   $$
--   (t,x)\longmapsto F_t(x)\text{ is }C^\infty,\qquad F_0=f,\quad F_1=g.
--   $$
--
--   The interval has its standard manifold-with-boundary model. The bundle constructs constant isotopies, reversal of time, and composition through a fixed intermediate diffeomorphism. These supply an equivalence relation on diffeomorphisms and its quotient of smooth-isotopy classes.
--
--   This is reusable smooth-isotopy infrastructure, not Cerf's theorem, isotopy extension, smooth gluing invariance, sphere recognition, or an SP4 implication. No finite-dimensionality, connectedness, Hausdorffness or additional manifold-compatibility typeclass is required by these declarations. Joint smoothness of the inverse family is not a separate field of the definition.
-- source:
--   Ryan Shin, unpublished Lean research source Isotopy.lean (2026), definitions Diffeotopy, Diffeotopy.refl/symm/trans, Isotopic, isotopySetoid and IsotopyClasses, lines 33–118; SHA-256 5c3ef5532fc26dce842c963bf7bc2d902692f11ab112839e9afbb79e8273fee5. Extracted using the official Lean declaration and source-span oracles. The admitted Cerf statement at lines 129–151 is omitted.

import Mathlib

/-! Smooth families of diffeomorphisms and their isotopy classes.
Extracted from Ryan Shin, Isotopy.lean, by official declaration oracles.
The admitted Cerf statement is omitted. -/
namespace SP4Isotopy

open Set Metric

open scoped Manifold ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A **smooth isotopy** between diffeomorphisms `φ ψ : M ≃ₘ M'`: a family of
diffeomorphisms over `[0, 1]`, jointly smooth in `(t, x)` as a map on the
product manifold-with-boundary `Icc 0 1 × M`, agreeing with `φ` at `0` and
`ψ` at `1`. -/
structure Diffeotopy (φ ψ : M ≃ₘ⟮I, I'⟯ M') where
  /-- The family of diffeomorphisms. -/
  slice : Set.Icc (0 : ℝ) 1 → (M ≃ₘ⟮I, I'⟯ M')
  /-- Joint smoothness in time and space. -/
  contMDiff : ContMDiff ((𝓡∂ 1).prod I) I' ∞
    (fun p : (Set.Icc (0 : ℝ) 1) × M => slice p.1 p.2)
  slice_bot : slice ⊥ = φ
  slice_top : slice ⊤ = ψ

namespace Diffeotopy

/-- The constant isotopy: every diffeomorphism is isotopic to itself. -/
def refl (φ : M ≃ₘ⟮I, I'⟯ M') : Diffeotopy φ φ where
  slice _ := φ
  contMDiff := φ.contMDiff.comp contMDiff_snd
  slice_bot := rfl
  slice_top := rfl


/-- Time reversal of the unit interval, `t ↦ 1 - t`. -/
def intervalRev (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.val, ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩

lemma contMDiff_intervalRev : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ intervalRev := by
  refine (contMDiff_iff_comp_subtypeVal_Icc (f := intervalRev)).mpr ⟨?_, ?_⟩
  · exact Continuous.subtype_mk
      (continuous_const.sub continuous_subtype_val) _
  · exact contMDiff_const.sub contMDiff_subtypeVal_Icc

/-- Reversing a smooth isotopy: if `φ` is isotopic to `ψ`, then `ψ` is
isotopic to `φ`. -/
def symm {φ ψ : M ≃ₘ⟮I, I'⟯ M'} (h : Diffeotopy φ ψ) :
    Diffeotopy ψ φ where
  slice t := h.slice (intervalRev t)
  contMDiff := h.contMDiff.comp (contMDiff_intervalRev.prodMap contMDiff_id)
  slice_bot := by
    rw [show intervalRev ⊥ = ⊤ from Subtype.ext (by simp [intervalRev])]
    exact h.slice_top
  slice_top := by
    rw [show intervalRev ⊤ = ⊥ from Subtype.ext (by simp [intervalRev])]
    exact h.slice_bot


/-- **Transitivity of smooth isotopy**, by pointwise composition: the family
`t ↦ h₂(t) ∘ ψ⁻¹ ∘ h₁(t)` runs from `φ` to `χ`, jointly smooth as a
composition of smooth families — no concatenation seam, no reparametrization
needed. (For π₀ purposes — all that Cerf-style gluing arguments use — this
is interchangeable with the classical concatenation.) -/
def trans {φ ψ χ : M ≃ₘ⟮I, I'⟯ M'} (h₁ : Diffeotopy φ ψ)
    (h₂ : Diffeotopy ψ χ) : Diffeotopy φ χ where
  slice t := (h₁.slice t).trans (ψ.symm.trans (h₂.slice t))
  contMDiff := by
    have hinner : ContMDiff ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod I) ∞
        (fun p : (Set.Icc (0 : ℝ) 1) × M =>
          ((p.1, ψ.symm (h₁.slice p.1 p.2)) : (Set.Icc (0 : ℝ) 1) × M)) :=
      contMDiff_fst.prodMk ((ψ.symm.contMDiff).comp h₁.contMDiff)
    exact h₂.contMDiff.comp hinner
  slice_bot := by
    rw [h₁.slice_bot, h₂.slice_bot, Diffeomorph.symm_trans_self,
      Diffeomorph.trans_refl]
  slice_top := by
    rw [h₁.slice_top, h₂.slice_top]
    ext x
    simp

end Diffeotopy

/-- The isotopy relation on diffeomorphisms, as a `Prop`. -/
def Isotopic (φ ψ : M ≃ₘ⟮I, I'⟯ M') : Prop := Nonempty (Diffeotopy φ ψ)

/-- Smooth isotopy is an equivalence relation on diffeomorphisms. -/
def isotopySetoid : Setoid (M ≃ₘ⟮I, I'⟯ M') where
  r := Isotopic
  iseqv := ⟨fun φ => ⟨Diffeotopy.refl φ⟩,
    fun ⟨h⟩ => ⟨h.symm⟩,
    fun ⟨h₁⟩ ⟨h₂⟩ => ⟨h₁.trans h₂⟩⟩

variable (I I' M M') in
/-- The type of smooth isotopy classes — for `M = M'`, `π₀` of the
diffeomorphism "group", the object Cerf's Γ₄ = 0 computes for `S³`. -/
def IsotopyClasses : Type _ :=
  Quotient (isotopySetoid (I := I) (I' := I') (M := M) (M' := M'))

end Diffeotopy

/-! ### The statement of Cerf's theorem Γ₄ = 0 -/

section Cerf





end Cerf

end
end SP4Isotopy


