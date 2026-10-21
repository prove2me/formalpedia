-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P09
-- name    : QAlgorithms_Papers_Independent_Renew46_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:02:16.83544+00:00
-- url     : https://prove2.me/theorems/5845f572-24de-4ee3-b123-23719224984c
-- title:
--   Definitions for On the characterization of trace class representations and Schwartz operators
-- statement:
--   The objects the formalized statements of *On the characterization of trace class representations and Schwartz operators* (arXiv:1512.02451) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasSmoothOrbit`: Smoothness of the actual orbit map, Introduction and Section 1, PDF pp.1,3. This definition uses a normed manifold model; its application below is finite dimensional. It does not supply a substitute for the nonnormable groups in Section 2.
--   - `integratedVector`: The integrated representation evaluated on a vector, PDF pp.2--3. The integral is taken in H, rather than in the operator-norm space B(H). The theorem supplies continuity and compact support of f and strong continuity of pi.
--   - `IsPositiveSelfAdjoint`: Positive self-adjoint partial operators, Proposition 2.1, PDF p.9. Self-adjointness is equality with the actual partial-map adjoint; positivity is nonnegativity of the quadratic form. No spectral lower bound is imposed.
--   - `SquareDomain`: The exact domain of A squared, Proposition 2.1, PDF p.9. A vector must be in D(A) and its first image must again be in D(A).
--   - `squareValue`: Apply A twice only on the domain on which both applications exist, Proposition 2.1, PDF p.9. No off-domain default is introduced.
-- source:
--   On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, https://arxiv.org/abs/1512.02451v1

import Mathlib

/-!
Statements from van Dijk--Neeb--Salmasian--Zellner, arXiv:1512.02451v1.
The representation statements here use the finite-dimensional setting of Section 1.
The pointwise-limit and interpolation statements have their own general settings.
Other nodes are individually deferred in the assigned unit's HARD.md and GAPS.json.
Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace QAlgorithms.Papers.Independent.Renew46.P09

/-- Smoothness of the actual orbit map, Introduction and Section 1, PDF pp.1,3.
This definition uses a normed manifold model; its application below is finite dimensional.
It does not supply a substitute for the nonnormable groups in Section 2. -/
def HasSmoothOrbit {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [ChartedSpace E G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (pi : G → H → H) (v : H) : Prop :=
  ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun g => pi g v)

/-- The integrated representation evaluated on a vector, PDF pp.2--3.
The integral is taken in H, rather than in the operator-norm space B(H).
The theorem supplies continuity and compact support of f and strong continuity of pi. -/
def integratedVector {G H : Type*} [MeasurableSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (mu : Measure G) (pi : G → H → H) (f : G → ℂ) (v : H) : H :=
  ∫ g, f g • pi g v ∂mu

/-- Sanity check: the zero test function gives the zero vector. -/
example {G H : Type*} [MeasurableSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (mu : Measure G) (pi : G → H → H) (v : H) :
    integratedVector mu pi (fun _ => 0) v = 0 := by
  simp [integratedVector]

/-- Sanity check: zero has a smooth orbit under every unitary representation. -/
example {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (pi : G →* (H ≃ₗᵢ[ℂ] H)) :
    HasSmoothOrbit (E := E) (fun g => pi g) (0 : H) := by
  simpa only [HasSmoothOrbit, map_zero] using
    (contMDiff_const : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, H) ∞ (fun _ : G => (0 : H)))

/-- Positive self-adjoint partial operators, Proposition 2.1, PDF p.9.
Self-adjointness is equality with the actual partial-map adjoint; positivity is
nonnegativity of the quadratic form. No spectral lower bound is imposed. -/
def IsPositiveSelfAdjoint {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
    (A : H →ₗ.[K] H) : Prop :=
  IsSelfAdjoint A ∧ ∀ v : A.domain, 0 ≤ RCLike.re (inner K (v : H) (A v))

/-- Sanity check: self-adjointness rules out a nondense junk-adjoint domain. -/
example {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
    (A : H →ₗ.[K] H) (hA : IsPositiveSelfAdjoint A) :
    Dense (A.domain : Set H) :=
  hA.1.dense_domain

/-- The exact domain of A squared, Proposition 2.1, PDF p.9.
A vector must be in D(A) and its first image must again be in D(A). -/
abbrev SquareDomain {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H] (A : H →ₗ.[K] H) :=
  {v : A.domain // A v ∈ A.domain}

/-- Apply A twice only on the domain on which both applications exist,
Proposition 2.1, PDF p.9. No off-domain default is introduced. -/
def squareValue {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H]
    (A : H →ₗ.[K] H) (v : SquareDomain A) : H :=
  A ⟨A v.val, v.property⟩

/-- Sanity check: the squared domain remembers both domain conditions. -/
example {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H]
    (A : H →ₗ.[K] H) (v : A.domain) :
    (∃ w : SquareDomain A, w.val = v) ↔ A v ∈ A.domain := by
  constructor
  · rintro ⟨w, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Sanity check: the squared operator sends its domain's zero to zero. -/
example {K H : Type*} [RCLike K]
    [NormedAddCommGroup H] [InnerProductSpace K H]
    (A : H →ₗ.[K] H) :
    squareValue A ⟨0, by simp⟩ = 0 := by
  change A ⟨A (0 : A.domain), _⟩ = 0
  have hz : (⟨A (0 : A.domain), by simp⟩ : A.domain) = 0 :=
    Subtype.ext A.map_zero
  exact (congrArg (fun v : A.domain => A v) hz).trans A.map_zero

end QAlgorithms.Papers.Independent.Renew46.P09


