-- Prove2me | Definitions.Def_ray_manifold_nontrivial
-- name    : ray_manifold_nontrivial
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T21:04:26.863116+00:00
-- url     : https://prove2.me/theorems/d434e086-fa58-4b02-805b-6e2f7559b067
-- title:
--   ray (7/12): inverse functions and nontrivial analytic maps on 1D manifolds
-- statement:
--   The analytic inverse function theorem for maps between one-dimensional complex manifolds, including a parameterised version. It proves that totally disconnected sets have no interior, and that a nontrivial analytic map has isolated level sets, together with their identity-theorem consequences. It also lifts Böttcher's local theorem to the manifold setting (`Super.bottcherNear`).
--
--   This file is part 7 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_bottcher_near

/-!
# ray (7/12): inverse functions and nontrivial analytic maps on 1D manifolds

Part 7 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Manifold.Inverse`
* `Ray.Misc.TotallyDisconnected`
* `Ray.Manifold.Nontrivial`
* `Ray.Dynamics.BottcherNearM`
-/

-- ===== Ray.Manifold.Inverse =====
section Ray_Ray_Manifold_Inverse
/-!
## The parameterized inverse function theorem on 1D complex manifolds

Given `f : ℂ × S → T`, we seek `g : ℂ × T → S` s.t. `g c (f c z) = z`.

The key theorems are `complex_inverse_fun` and `complex_inverse_fun'`; everything else is
intermediate lemmas.

These results are straightforward consequences of the 2D inverse function theorem
applied to `(c,z) ↦ (c, f c z)` mapped to charts, but (at least for me)
this takes a while to write out.  A subtlety is that `TangentSpace I z` for
`z ∈ ℂ` is definitionally and canonically `ℂ`, and we take advantage of this
to express manifold invertibility in charts as nonmanifold invertibility.  But
this means that the type signatures on all the small definitions are very important
to make `simp` go through correctly.
-/

open Classical
open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff OneDimension Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

namespace ComplexInverseFun

/-- Data for our 1D inverse function theorem -/
structure Cinv (f : ℂ → S → T) (c : ℂ) (z : S) : Prop where
  fa : ContMDiffAt II I ω (uncurry f) (c, z)
  nc : mfderiv I I (f c) z ≠ 0

variable {f : ℂ → S → T} {c : ℂ} {z : S}

/-- `z` in charts -/
@[nolint unusedArguments] def Cinv.z' (_ : Cinv f c z) : ℂ := extChartAt I z z

/-- `f z` in charts -/
@[nolint unusedArguments] def Cinv.fz' (_ : Cinv f c z) : ℂ := extChartAt I (f c z) (f c z)

lemma Cinv.zz (i : Cinv f c z) : (extChartAt I z).symm (c, i.z').snd = z := by
  simp only [Cinv.z', PartialEquiv.left_inv _ (mem_extChartAt_source _)]

/-- `f` in coordinates -/
@[nolint unusedArguments] def Cinv.f' (_ : Cinv f c z) : ℂ × ℂ → ℂ := fun x ↦
  extChartAt I (f c z) (f x.1 ((extChartAt I z).symm x.2))

/-- `(c,z) → (c, f c z)`, in coordinates.  We will show this function is invertible. -/
def Cinv.h (i : Cinv f c z) : ℂ × ℂ → ℂ × ℂ := fun x ↦ (x.1, i.f' x)

-- f' and h are analytic
theorem Cinv.fa' (i : Cinv f c z) : AnalyticAt ℂ i.f' (c, i.z') := by
  have fa := i.fa
  simp only [mAnalyticAt_iff_of_boundaryless, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm,
    PartialEquiv.prod_coe] at fa
  exact fa.2
theorem Cinv.ha (i : Cinv f c z) : AnalyticAt ℂ i.h (c, i.z') := analyticAt_fst.prod i.fa'

/-- The key nonzero derivative: `d(f c z)/dz` -/
@[nolint unusedArguments]
def Cinv.dfz (_ : Cinv f c z) : TangentSpace I z →L[ℂ] TangentSpace I (f c z) := mfderiv I I (f c) z

/-- The inverse of the key nonzero derivative: `(d(f c z)/dz)⁻¹` -/
def Cinv.dfzi (i : Cinv f c z) :
    TangentSpace I (f c z) →L[ℂ] TangentSpace I z := (mderivEquiv i.dfz i.nc).symm

lemma Cinv.dfzi_dfz (i : Cinv f c z) : ∀ t, i.dfzi (i.dfz t) = t :=
    fun _ ↦ (mderivEquiv _ i.nc).left_inv _
lemma Cinv.dfz_dfzi (i : Cinv f c z) : ∀ t, i.dfz (i.dfzi t) = t :=
    fun _ ↦ (mderivEquiv _ i.nc).right_inv _

-- The derivative i.dh of i.h
--   dh = dc.prod (i.de'.comp (i.dfc.comp dc + i.dfz.comp (i.de.comp dz)))
--      = (    1               0      )
--        (de' ∘ dfc    de' ∘ dfz ∘ de)

/-- The inverse chart derivative at `z` -/
def Cinv.de (i : Cinv f c z) : ℂ →L[ℂ] TangentSpace I z := mfderiv I I (extChartAt I z).symm i.z'
/-- The chart derivative at `f c z` -/
def Cinv.de' (_ : Cinv f c z) :
    TangentSpace I (f c z) →L[ℂ] ℂ := mfderiv I I (extChartAt I (f c z)) (f c z)
/-- The derivative of `(c,z) ↦ c` is `fst` -/
def dc : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ
/-- The derivative of `(c,z) ↦ z` is `snd` -/
def dz : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
/-- `d(f c z)/dc` -/
def Cinv.dfc (_ : Cinv f c z) : ℂ →L[ℂ] TangentSpace I (f c z) := mfderiv I I (fun c : ℂ ↦ f c z) c
/-- `df = d(f c z)/dc dc + d(f c z)/dz dz` -/
def Cinv.df (i : Cinv f c z) :
    ℂ × ℂ →L[ℂ] TangentSpace I (f c z) := i.dfc.comp dc + i.dfz.comp (i.de.comp dz)
/-- `df` in charts -/
def Cinv.df' (i : Cinv f c z) : ℂ × ℂ →L[ℂ] ℂ := i.de'.comp i.df
/-- `dh` (in charts) -/
def Cinv.dh (i : Cinv f c z) : ℂ × ℂ →L[ℂ] ℂ × ℂ := dc.prod i.df'

-- dh is invertible
--   dh (u,v) = (a,b)
--   (u, (de' ∘ dfc)u + (de' ∘ dfz ∘ de)v) = (a,b)
--   u = a
--   (de' ∘ dfc)a + (de' ∘ dfz ∘ de)v = b
--   v = (de' ∘ dfz ∘ de)⁻¹ (b - (de' ∘ dfc)a)
--   v = (de⁻¹  ∘ dfz⁻¹ ∘ de'⁻¹) (b - (de' ∘ dfc)a)
/-- The chart derivative at `z` -/
def Cinv.dei (_ : Cinv f c z) :
    TangentSpace I z →L[ℂ] ℂ := mfderiv I I (extChartAt I z) z
/-- The inverse chart derivative at `z` -/
def Cinv.dei' (i : Cinv f c z) :
    ℂ →L[ℂ] TangentSpace I (f c z) := mfderiv I I (extChartAt I (f c z)).symm i.fz'
/-- The key inverse derivative of `f` w.r.t. `z`, in charts -/
def Cinv.dfi' (i : Cinv f c z) : ℂ →L[ℂ] ℂ := (i.dei.comp i.dfzi).comp i.dei'
/-- The overall inverse derivative of `h` -/
def Cinv.dhi (i : Cinv f c z) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ := dc.prod (i.dfi'.comp (dz - (i.de'.comp i.dfc).comp dc))

variable [cms : IsManifold I ω S]

lemma Cinv.dei_de (i : Cinv f c z) : ∀ t, i.dei (i.de t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp
    (extChartAt_mderiv_right_inverse' (mem_extChartAt_source (I := I) z)) t
  exact h

variable [cmt : IsManifold I ω T]

lemma Cinv.has_df' (i : Cinv f c z) : HasMFDerivAt II I i.f' (c, i.z') i.df' := by
  apply HasMFDerivAt.comp (I' := I) (c, i.z')
  · rw [i.zz]
    exact ((contMDiffAt_extChartAt' (mem_chart_source _ _)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  · simp only [Cinv.df]
    have fd := i.fa.mdifferentiableAt (by decide)
    rw [← i.zz] at fd
    apply MDifferentiableAt.hasMFDerivAt_comp2 fd
    · apply hasMFDerivAt_fst
    · refine HasMFDerivAt.comp _ ?_ (hasMFDerivAt_snd _)
      exact (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds'
        (mem_extChartAt_target _))).mdifferentiableAt one_ne_zero).hasMFDerivAt
    · rw [i.zz]; exact (i.fa.along_fst.mdifferentiableAt (by decide)).hasMFDerivAt
    · rw [i.zz]; exact (i.fa.along_snd.mdifferentiableAt (by decide)).hasMFDerivAt

lemma Cinv.has_dh (i : Cinv f c z) : HasMFDerivAt II II i.h (c, i.z') i.dh := by
  refine HasMFDerivAt.prodMk ?_ i.has_df'; apply hasMFDerivAt_fst

omit cms in
lemma Cinv.dei_de' (i : Cinv f c z) : ∀ t, i.dei' (i.de' t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse
    (mem_extChartAt_source (f c z))) t
  simp only [ContinuousLinearMap.comp_apply] at h; exact h

omit cmt in
lemma Cinv.de_dei (i : Cinv f c z) : ∀ t, i.de (i.dei t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse
    (mem_extChartAt_source z)) t
  simp only [ContinuousLinearMap.comp_apply] at h; exact h

omit cms in
lemma Cinv.de_dei' (i : Cinv f c z) : ∀ t, i.de' (i.dei' t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_right_inverse'
    (mem_extChartAt_source (I := I) (f c z))) t
  exact h

lemma Cinv.dhi_dh (i : Cinv f c z) : ∀ t, i.dhi (i.dh t) = t := by
  intro ⟨u, v⟩
  simp only [Cinv.dh, Cinv.dhi, dc, dz, Cinv.dfi', Cinv.df', Cinv.df, i.dei_de', i.dei_de,
    i.dfzi_dfz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    _root_.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    _root_.add_apply, ContinuousLinearMap.map_add, add_sub_cancel_left]

lemma Cinv.dh_dhi (i : Cinv f c z) : ∀ t, i.dh (i.dhi t) = t := by
  intro ⟨u, v⟩
  simp only [Cinv.dh, Cinv.dhi, dc, dz, Cinv.dfi', Cinv.df', Cinv.df, i.de_dei', i.de_dei,
    i.dfz_dfzi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    _root_.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    _root_.add_apply, ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
    add_sub_cancel_left, ← add_sub_assoc]

/-- `dh` as a `ContinuousLinearEquiv` -/
def Cinv.dhe (i : Cinv f c z) : (ℂ × ℂ) ≃L[ℂ] ℂ × ℂ :=
  ContinuousLinearEquiv.equivOfInverse i.dh i.dhi i.dhi_dh i.dh_dhi

lemma Cinv.has_dhe (i : Cinv f c z) : HasFDerivAt i.h (i.dhe : ℂ × ℂ →L[ℂ] ℂ × ℂ) (c, i.z') :=
  hasMFDerivAt_iff_hasFDerivAt'.mp i.has_dh

/-- `h` as a `PartialHomeomorph` -/
def Cinv.he (i : Cinv f c z) :=
  ContDiffAt.toOpenPartialHomeomorph i.h i.ha.contDiffAt i.has_dhe one_ne_zero

/-- `h` inverts at the point -/
theorem Cinv.inv_at (i : Cinv f c z) :
    (i.he.symm (c, extChartAt I (f c z) (f c z))).2 = extChartAt I z z := by
  have a := ContDiffAt.localInverse_apply_image i.ha.contDiffAt i.has_dhe one_ne_zero
  have e : ContDiffAt.localInverse i.ha.contDiffAt i.has_dhe one_ne_zero = i.he.symm := rfl
  rw [e] at a; clear e
  simp only [Cinv.z', Cinv.h, Cinv.f', PartialEquiv.left_inv _ (mem_extChartAt_source _)] at a
  rw [a]

/-- Our inverse function! -/
def Cinv.g (i : Cinv f c z) : ℂ → T → S := fun b w ↦
  (extChartAt I z).symm (i.he.symm (b, extChartAt I (f c z) w)).2

/-- `g` is a local left inverse -/
theorem Cinv.left_inv (i : Cinv f c z) : ∀ᶠ x : ℂ × S in 𝓝 (c, z), i.g x.1 (f x.1 x.2) = x.2 := by
  generalize ht :
      ((extChartAt II (c, z)).source ∩ extChartAt II (c, z) ⁻¹' i.he.source : Set (ℂ × S)) = t
  have o : IsOpen t := by
    rw [← ht]
    exact (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
      i.he.open_source
  have m : (c, z) ∈ t := by
    simp only [mem_inter_iff, mem_preimage, mem_extChartAt_source, true_and, ← ht]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source i.ha.contDiffAt i.has_dhe one_ne_zero
  apply Filter.eventuallyEq_of_mem (o.mem_nhds m); intro x m
  simp only [mem_inter_iff, mem_preimage, extChartAt_prod, extChartAt_eq_refl, ← ht,
    PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod_eq, mem_univ, true_and,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id] at m
  have inv := i.he.left_inv m.2
  simp only [Cinv.g]
  generalize hq : i.he.symm = q; rw [hq] at inv
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero] at inv
  simp only [Cinv.h, Cinv.f', PartialEquiv.left_inv _ m.1] at inv
  simp only [inv, PartialEquiv.left_inv _ m.1]

/-- `h⁻¹` passes through its first argument -/
theorem Cinv.inv_fst (i : Cinv f c z) : ∀ x, x ∈ i.he.target → (i.he.symm x).1 = x.1 := by
  intro x m
  have e : i.he (i.he.symm x) = x := i.he.right_inv m
  generalize hq : i.he.symm x = q; rw [hq] at e
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero,
    Cinv.h] at e
  rw [← e]

/-- `g` is a local right inverse -/
theorem Cinv.right_inv (i : Cinv f c z) :
    ∀ᶠ x : ℂ × T in 𝓝 (c, f c z), f x.1 (i.g x.1 x.2) = x.2 := by
  generalize ht : ((extChartAt II (c, f c z)).source ∩ extChartAt II (c, f c z) ⁻¹' i.he.target
      : Set (ℂ × T)) = t
  have o : IsOpen t := by
    rw [← ht]
    exact (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
      i.he.open_target
  have m' : (c, extChartAt I (f c z) (f c z)) ∈ i.he.toPartialEquiv.target := by
    have m := ContDiffAt.image_mem_toOpenPartialHomeomorph_target i.ha.contDiffAt i.has_dhe
      one_ne_zero
    have e : i.h (c, i.z') = (c, extChartAt I (f c z) (f c z)) := by
      simp only [Cinv.h, Cinv.z', Cinv.f', PartialEquiv.left_inv _ (mem_extChartAt_source _)]
    rw [e] at m; exact m
  have m : (c, f c z) ∈ t := by
    simp only [m', mem_inter_iff, mem_preimage, mem_extChartAt_source, true_and, ← ht,
      extChartAt_prod, PartialEquiv.prod_coe, extChartAt_eq_refl, PartialEquiv.refl_coe, id,
      PartialEquiv.prod_source, prodMk_mem_set_prod_eq, PartialEquiv.refl_source, mem_univ]
  have fm : ∀ᶠ x : ℂ × T in 𝓝 (c, f c z),
      f x.1 ((extChartAt I z).symm (i.he.symm (x.1, extChartAt I (f c z) x.2)).2) ∈
        (extChartAt I (f c z)).source := by
    refine ContinuousAt.eventually_mem ?_ (extChartAt_source_mem_nhds' ?_)
    · apply i.fa.continuousAt.comp₂_of_eq continuousAt_fst
      · refine ContinuousAt.comp ?_ ?_
        · simp only [i.inv_at]; exact continuousAt_extChartAt_symm _
        · apply continuousAt_snd.comp
          · refine (OpenPartialHomeomorph.continuousAt i.he.symm ?_).comp ?_
            · simp only [m', (he i).symm_source]
            · apply continuousAt_fst.prodMk
              apply (continuousAt_extChartAt _).comp_of_eq
              · exact continuousAt_snd
              · rfl
      · simp only [i.inv_at, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
    · simp only [i.inv_at, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
      apply mem_extChartAt_source
  refine fm.mp (Filter.eventually_of_mem (o.mem_nhds m) ?_)
  intro x m mf
  simp only [mem_inter_iff, mem_preimage, extChartAt_prod, extChartAt_eq_refl,
    PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod_eq, mem_univ, true_and,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, ← ht] at m
  have inv := i.he.right_inv m.2
  simp only [Cinv.g]
  generalize hq : i.he.symm = q; rw [hq] at inv mf
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero] at inv
  have q1 : (q (x.1, extChartAt I (f c z) x.2)).1 = x.1 := by simp only [← hq, i.inv_fst _ m.2]
  simp only [Cinv.h, Cinv.f', Prod.eq_iff_fst_eq_snd_eq, q1] at inv
  nth_rw 2 [← PartialEquiv.left_inv _ m.1]; nth_rw 2 [← inv.2]
  refine (PartialEquiv.left_inv _ mf).symm

theorem Cinv.he_symm_mAnalytic (i : Cinv f c z) : ContMDiffAt II II ω i.he.symm (c, i.fz') := by
  have d : ContDiffAt ℂ ω i.he.symm _ :=
    ContDiffAt.to_localInverse i.ha.contDiffAt i.has_dhe (by decide)
  have e : i.h (c, i.z') = (c, i.fz') := by
    simp only [Cinv.h, Cinv.fz', Cinv.f']
    simp only [Cinv.z', (extChartAt I z).left_inv (mem_extChartAt_source _)]
  rw [e] at d
  rw [← analyticAt_iff_mAnalyticAt]
  exact (contDiffAt_iff_analytic_at2 le_top).mp d

/-- Our inverse `g` is analytic -/
theorem Cinv.ga (i : Cinv f c z) : ContMDiffAt II I ω (uncurry i.g) (c, f c z) := by
  apply ((contMDiffOn_extChartAt_symm _).contMDiffAt
    (extChartAt_target_mem_nhds' (mem_extChartAt_target z))).comp_of_eq
  · refine contMDiffAt_snd.comp _ (i.he_symm_mAnalytic.comp_of_eq ?_ ?_)
    · apply contMDiffAt_fst.prodMk
      refine (contMDiffAt_extChartAt' ?_).comp _ contMDiffAt_snd
      exact mem_chart_source _ _
    · rfl
  · exact i.inv_at

end ComplexInverseFun

variable [IsManifold I ω S] [IsManifold I ω T]

/-- The 1D inverse function theorem for complex manifolds (parameterized version):
    If `f : ℂ → S → T` is analytic with nonzero derivative (w.r.t. the second
    argument) at a point `(c,z)`, it is a parameterized local inverse `g : ℂ → T → S` s.t.
    `g c (f c z) = z` and `f c (g c z) = z` locally. -/
theorem complex_inverse_fun {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∃ g : ℂ → T → S,
      ContMDiffAt II I ω (uncurry g) (c, f c z) ∧
        (∀ᶠ x : ℂ × S in 𝓝 (c, z), g x.1 (f x.1 x.2) = x.2) ∧
          ∀ᶠ x : ℂ × T in 𝓝 (c, f c z), f x.1 (g x.1 x.2) = x.2 := by
  have i : ComplexInverseFun.Cinv f c z :=
    { fa
      nc }
  use i.g, i.ga, i.left_inv, i.right_inv

/-- The 1D inverse function theorem for complex manifolds (nonparameterized version):
    If `f : S → T` is analytic with nonzero derivative, it has a local inverse `g : T → S`. -/
theorem complex_inverse_fun' {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z)
    (nc : mfderiv I I f z ≠ 0) :
    ∃ g : T → S,
      ContMDiffAt I I ω g (f z) ∧ (∀ᶠ x in 𝓝 z, g (f x) = x) ∧ ∀ᶠ x in 𝓝 (f z), f (g x) = x := by
  set f' : ℂ → S → T := fun _ z ↦ f z
  have fa' : ContMDiffAt II I ω (uncurry f') (0, z) := fa.comp_of_eq contMDiffAt_snd rfl
  rcases complex_inverse_fun fa' nc with ⟨g, ga, gf, fg⟩
  use g 0, ga.comp _ (contMDiffAt_const.prodMk contMDiffAt_id),
    (continuousAt_const.prodMk continuousAt_id).eventually gf,
    (continuousAt_const.prodMk continuousAt_id).eventually fg

end
end Ray_Ray_Manifold_Inverse

-- ===== Ray.Misc.TotallyDisconnected =====
section Ray_Ray_Misc_TotallyDisconnected
/-!
## Countable sets and space are totally disconnected
-/

open Classical
open Function (uncurry)
open Metric (ball closedBall mem_ball mem_closedBall isOpen_ball isClosed_closedBall mem_ball_self)
open Set
open scoped Topology
noncomputable section

/-- A left inverse to subtype coe -/
def Set.Nonempty.invCoe {X : Type} {s : Set X} (ne : s.Nonempty) : X → s := fun x ↦
  if m : x ∈ s then (⟨x, m⟩ : s) else (⟨ne.some, ne.some_mem⟩ : s)

theorem Set.Nonempty.left_invCoe {X : Type} {s : Set X} (ne : s.Nonempty) :
    ∀ x : s, ne.invCoe x = x := by
  intro ⟨x, m⟩; simp only [Set.Nonempty.invCoe, m, dif_pos]

theorem Set.Nonempty.right_invCoe {X : Type} {s : Set X} (ne : s.Nonempty) :
    ∀ x, x ∈ s → ↑(ne.invCoe x) = x := by
  intro x m; simp only [Set.Nonempty.invCoe, m, dif_pos, Subtype.coe_mk]

theorem Set.Nonempty.continuousOn_invCoe {X : Type} {s : Set X} (ne : s.Nonempty)
    [TopologicalSpace X] : ContinuousOn ne.invCoe s := by
  rw [Topology.IsEmbedding.subtypeVal.continuousOn_iff]
  apply continuousOn_id.congr
  intro x m
  simp only [Function.comp, ne.right_invCoe _ m, id]

/-- `IsTotallyDisconnected` is the same as `TotallyDisconnectedSpace` on the subtype -/
theorem isTotallyDisconnected_iff_totally_disconnected_subtype {X : Type} [TopologicalSpace X]
    {s : Set X} : TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  constructor
  · intro h
    by_cases ne : s.Nonempty
    · intro t ts tc
      set t' := ne.invCoe '' t
      have tc' : IsPreconnected t' := tc.image _ (ne.continuousOn_invCoe.mono ts)
      have q := h.isTotallyDisconnected_univ _ (subset_univ _) tc'
      have e : t = (fun x : s ↦ x.val) '' t' := by
        apply Set.ext; intro x; simp only [mem_image]; constructor
        · intro xt; use ⟨x, ts xt⟩; refine ⟨⟨x,xt,?_⟩,?_⟩
          simp only [Subtype.ext_iff, ne.right_invCoe _ (ts xt)]
          rw [Subtype.coe_mk]
        · intro ⟨⟨y, ys⟩, ⟨z, zt, zy⟩, yx⟩
          simp only [Subtype.ext_iff, ne.right_invCoe _ (ts zt)] at yx zy
          rw [← yx, ← zy]; exact zt
      rw [e]; exact q.image _
    · simp only [not_nonempty_iff_eq_empty] at ne; rw [ne]; exact isTotallyDisconnected_empty
  · intro h
    refine ⟨?_⟩
    apply Topology.IsEmbedding.subtypeVal.isTotallyDisconnected
    rw [Subtype.coe_image_univ]; exact h

/-- `Ioo` on the reals is not countable if it is nonempty -/
theorem not_countable_Ioo {a b : ℝ} (h : a < b) : ¬(Ioo a b).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, not_le, Cardinal.mk_Ioo_real h]; apply Cardinal.cantor

/-- Countable metric spaces are totally disconnected -/
theorem Countable.totallyDisconnectedSpace {X : Type} [MetricSpace X] [Countable X] :
    TotallyDisconnectedSpace X := by
  generalize hR : {r | ∃ x y : X, dist x y = r} = R
  have rc : R.Countable := by
    have e : R = range (uncurry (dist (α := X))) := by
      apply Set.ext; intro r; simp only [mem_ofPred, mem_range, Prod.exists, uncurry, ← hR]
    rw [e]; exact countable_range _
  refine @TotallySeparatedSpace.totallyDisconnectedSpace _ _ ?_
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y xy
  rw [← dist_pos] at xy
  have h : ¬Ioo 0 (dist x y) ⊆ R := by by_contra h; exact not_countable_Ioo xy (rc.mono h)
  simp only [not_subset, mem_Ioo] at h; rcases h with ⟨r, ⟨rp, rxy⟩, rr⟩
  have e : ball x r = closedBall x r := by
    apply Set.ext; intro z; simp only [mem_ball, mem_closedBall]
    simp only [mem_ofPred, not_exists, ← hR] at rr; simp only [Ne.le_iff_lt (rr z x)]
  refine ⟨ball x r, ⟨?_, isOpen_ball⟩, ?_⟩
  rw [e]; exact isClosed_closedBall; use mem_ball_self rp
  simp only [mem_compl_iff, mem_ball, dist_comm, not_lt]
  exact rxy.le

/-- Countable sets are totally disconnected -/
theorem IsCountable.isTotallyDisconnected {X : Type} [MetricSpace X] {s : Set X}
    (h : s.Countable) : IsTotallyDisconnected s := by
  rw [← isTotallyDisconnected_iff_totally_disconnected_subtype]
  exact @Countable.totallyDisconnectedSpace _ _ (countable_coe_iff.mpr h)

end
end Ray_Ray_Misc_TotallyDisconnected

-- ===== Ray.Manifold.Nontrivial =====
section Ray_Ray_Manifold_Nontrivial
/-!
## Nontriviality of analytic functions, and consequences

We define several structures representing global and local nontriviality (nonconstness)
of analytic and analytic functions, and in 1D or parameterized 1D:

1. `NontrivialAnalyticOn f s`: Near every point `z ∈ s`, `f` is locally analytic and nonconstant
1. `NontrivialMAnalyticOn f s`: The same for analytic functions between 1D analytic manifolds
2. `NontrivialMAnalyticAt f z`: Near `z`, `f` is analytic and nonconstant

These "everyone nontrivial" properties can be derived from properties at one point:

1. If an analytic function is nonconstant on a preconnected set, is it nontrivial there
2. Nonzero analytic derivative implies nontriviality
3. Nontriviality is preserved by composition
4. If a composition is nontrivial, both parts are nontrivial
5. `id` is nontrivial
6. Positive `orderAt` implies nontrivial

From these, we have a variety of consequences, such as:

1. Nontrivial functions have isolated zeros or other values.
2. The zeros (or preimages of another value) of a nontrivial function have a discrete topology
3. Pow is nontrivial, so roots of unity are totally disconnected
4. If a nontrivial function is constant on the image of a preconnected set, the image is a singleton
5. Near a point, analytic functions are either locally constant or locally ≠ to the point value
6. Locally constant functions are constant on preconnected sets
-/

open Classical
open Filter (Tendsto)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball mem_ball mem_closedBall mem_ball_self
  mem_closedBall_self mem_sphere sphere)
open OneDimension
open Set
open scoped ContDiff OneDimension Real Topology Manifold
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [ChartedSpace ℂ U]

section Nontrivial

variable {f : ℂ → ℂ} {s : Set ℂ}

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ f z := by
  have fa : AnalyticAt ℂ (fun w ↦ f w - f z) z := (n.analyticOn z zs).sub analyticAt_const
  cases' fa.eventually_eq_zero_or_eventually_ne_zero with h h
  · have b := h.and_frequently (n.nonconst z zs)
    simp only [sub_eq_zero, Ne, and_not_self_iff, Filter.frequently_false] at b
  · simp only [sub_ne_zero] at h; exact h

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated' (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) (a : ℂ) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ a := by
  by_cases h : f z = a; simp only [← h]; exact n.isolated zs
  exact ((n.analyticOn _ zs).continuousAt.eventually_ne h).filter_mono nhdsWithin_le_nhds

/-- Nonconstant functions on preconnected sets are nontrivial -/
theorem IsPreconnected.nontrivialAnalyticOn (p : IsPreconnected s) (fa : AnalyticOnNhd ℂ f s)
    (ne : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a ≠ f b) : NontrivialAnalyticOn f s :=
  { analyticOn := fa
    nonconst := by
      contrapose ne; simp only [not_forall, Filter.not_frequently, not_not] at ne
      rcases ne with ⟨z, zs, h⟩
      simp only [not_exists, exists_and_left, not_and, not_not]
      have h' := (h.filter_mono (nhdsWithin_le_nhds (s := {z}ᶜ))).frequently
      have e := fa.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const p zs h'
      intro x xs y ys; rw [e xs, e ys] }

/-- Nonconstant entire functions are nontrivial -/
theorem Entire.nontrivialAnalyticOn (fa : AnalyticOnNhd ℂ f univ) (ne : ∃ a b, f a ≠ f b) :
    NontrivialAnalyticOn f univ := by
  refine isPreconnected_univ.nontrivialAnalyticOn fa ?_; simpa only [Set.mem_univ, true_and]

/-- The roots of a nontrivial analytic function form a discrete topology -/
theorem NontrivialAnalyticOn.discreteTopology (n : NontrivialAnalyticOn f s) (a : ℂ) :
    DiscreteTopology (↥(s ∩ f ⁻¹' {a})) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro ⟨z, m⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
  by_cases h : ∃ᶠ z in 𝓝[{z}ᶜ] z, f z = a
  · have i := (n.isolated' m.1 a).and_frequently h
    simp only [not_and_self_iff, Filter.frequently_const] at i
  · simp only [Filter.not_frequently, eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
    rcases eventually_nhds_iff.mp h with ⟨t, t0, o, tz⟩
    simp only [isOpen_induced_iff]; use t, o
    apply Set.ext; intro ⟨w, m⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk_eq_mk]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
    specialize t0 w
    simp only [m.2, imp_false, not_true, not_not] at t0
    use t0; intro wz; rw [wz]; exact tz

/-- pow is nontrivial -/
theorem powNontrivial {d : ℕ} (dp : 0 < d) : NontrivialAnalyticOn (fun z ↦ z ^ d) univ := by
  apply Entire.nontrivialAnalyticOn fun _ _ ↦ analyticAt_id.pow _; use 0, 1
  simp only [id, one_pow, zero_pow (Nat.pos_iff_ne_zero.mp dp), Pi.pow_def]; norm_num

/-- All roots of unity as a set -/
def allRootsOfUnity :=
  {z : ℂ | ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1}

/-- Roots of unity are nonzero -/
theorem allRootsOfUnity.ne_zero {z : ℂ} (m : z ∈ allRootsOfUnity) : z ≠ 0 := by
  rcases m with ⟨n, n0, z1⟩; contrapose z1
  simp only [z1, zero_pow n0]; exact zero_ne_one

/-- Roots of unity are totally disconnected -/
theorem IsTotallyDisconnected.allRootsOfUnity : IsTotallyDisconnected allRootsOfUnity := by
  apply IsCountable.isTotallyDisconnected
  simp only [_root_.allRootsOfUnity, ofPred_exists]; apply countable_iUnion; intro n
  by_cases n0 : n = 0
  simp only [n0, Ne, not_true, false_and, ofPred_false, countable_empty]
  simp only [Ne, n0, not_false_iff, true_and]
  have np : 0 < n := Nat.pos_of_ne_zero n0
  generalize hn' : (⟨n, np⟩ : ℕ+) = n'
  have e : {z : ℂ | z ^ n = 1} ⊆ (fun x : ℂˣ ↦ (x : ℂ)) '' (rootsOfUnity n' ℂ : Set ℂˣ) := by
    intro z e; simp only [mem_ofPred] at e
    simp only [mem_image, SetLike.mem_coe]
    by_cases z0 : z = 0
    · simp only [z0, zero_pow n0, zero_ne_one] at e
    · use Units.mk0 z z0
      simp [← hn', ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_mk0, e, Units.val_one,
        and_self]
  apply Set.Countable.mono e; clear e; apply Countable.image
  have : NeZero (n' : ℕ) := ⟨n'.2.ne'⟩
  have h : (rootsOfUnity (n' : ℕ) ℂ : Set ℂˣ).Finite :=
    Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity (n' : ℕ) ℂ)))
  exact h.countable

/-- Given continuous `p : X → ℂ` on preconnected `X`, `p` is const if `f ∘ p` is const -/
theorem NontrivialAnalyticOn.const (n : NontrivialAnalyticOn f s) {p : X → ℂ} {t : Set X}
    (tc : IsPreconnected t) (pc : ContinuousOn p t) (ps : Set.MapsTo p t s) {a b : ℂ}
    (p1 : ∃ x, x ∈ t ∧ p x = a) (fp : ∀ x, x ∈ t → f (p x) = b) : ∀ x, x ∈ t → p x = a := by
  have disc : DiscreteTopology (↥(s ∩ f ⁻¹' {b})) := n.discreteTopology b
  rcases p1 with ⟨z, zt, z1⟩; simp only [← z1]
  intro x xt
  refine @IsPreconnected.constant_of_mapsTo _ _ _ tc _ _ _ disc.isDiscrete _ pc ?_ _ _ xt zt
  intro y yt; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  use ps yt, fp _ yt

/-- Given `p : X → ℂ`, `p^d = 1 → p = 1` given continuity, `X` preconnected,
    and `p = 1` somewhere -/
theorem eq_one_of_pow_eq_one {p : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (tc : IsPreconnected t) (dp : d > 0) (pa : ∃ x, x ∈ t ∧ p x = 1)
    (pd : ∀ x, x ∈ t → p x ^ d = 1) : ∀ x, x ∈ t → p x = 1 :=
  (powNontrivial dp).const tc pc (Set.mapsTo_univ _ _) pa pd

/-- Given `p, q : X → ℂ`, `p^d = q^d → p ≠ 0 → p = q` -/
theorem eq_of_pow_eq {p q : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (qc : ContinuousOn q t) (tc : IsPreconnected t) (dp : d > 0) (pq : ∃ x, x ∈ t ∧ p x = q x)
    (p0 : ∀ x, x ∈ t → p x ≠ 0) (pqd : ∀ x, x ∈ t → p x ^ d = q x ^ d) :
    ∀ x, x ∈ t → p x = q x := by
  generalize hr : (fun x ↦ q x / p x) = r
  have rc : ContinuousOn r t := by rw [← hr]; exact qc.div pc p0
  have h := eq_one_of_pow_eq_one rc tc dp ?_ ?_
  · intro x m
    rw [← hr] at h
    exact ((div_eq_one_iff_eq (p0 _ m)).mp (h _ m)).symm
  · rcases pq with ⟨x, m, e⟩; use x, m
    rw [← hr]
    exact (div_eq_one_iff_eq (p0 _ m)).mpr e.symm
  · intro x m
    simp only [div_pow, ← hr]
    rw [div_eq_one_iff_eq]
    · exact (pqd _ m).symm
    · exact pow_ne_zero _ (p0 _ m)

/-- At a point, a analytic function is either locally constant or locally different from its
    value at the point.  This is the `ContMDiffAt` version of
    `AnalyticAt.eventuallyEq_or_eventually_ne` -/
theorem ContMDiffAt.eventually_eq_or_eventually_ne [T2Space T] {f g : S → T} {z : S}
    (fa : ContMDiffAt I I ω f z) (ga : ContMDiffAt I I ω g z) :
    (∀ᶠ w in 𝓝 z, f w = g w) ∨ ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ g w := by
  simp only [mAnalyticAt_iff_of_boundaryless, Function.comp_def] at fa ga
  rcases fa with ⟨fc, fa⟩; rcases ga with ⟨gc, ga⟩
  by_cases fg : f z ≠ g z
  · right; contrapose fg
    simp only [Filter.not_eventually, not_not] at fg
    exact tendsto_nhds_unique_of_frequently_eq fc gc (fg.filter_mono nhdsWithin_le_nhds)
  simp only [not_not] at fg
  cases' fa.eventually_eq_or_eventually_ne ga with e e
  · left; clear fa ga
    replace e := (continuousAt_extChartAt z).eventually e
    replace e := Filter.EventuallyEq.fun_comp e (_root_.extChartAt I (f z)).symm
    apply e.congr; simp only [Function.comp_def]; clear e
    apply (fc.eventually_mem (extChartAt_source_mem_nhds (I := I) (f z))).mp
    apply (gc.eventually_mem (extChartAt_source_mem_nhds (I := I) (g z))).mp
    refine eventually_nhds_iff.mpr ⟨(_root_.extChartAt I z).source,
      fun x m gm fm ↦ ?_, isOpen_extChartAt_source _, mem_extChartAt_source z⟩
    rw [← fg] at gm
    simp only [← fg, PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ fm,
      PartialEquiv.left_inv _ gm]
  · right; clear fa ga
    simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at e ⊢
    replace e := (continuousAt_extChartAt z).eventually e
    apply (fc.eventually_mem ((extChartAt_source_mem_nhds (I := I) (f z)))).mp
    apply (gc.eventually_mem ((extChartAt_source_mem_nhds (I := I) (g z)))).mp
    apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
    refine e.mp (.of_forall ?_); clear e
    intro x h xm gm fm xz; rw [← fg] at gm
    simp only [← fg, PartialEquiv.left_inv _ xm] at h
    specialize h ((PartialEquiv.injOn _).ne xm (mem_extChartAt_source _) xz)
    rwa [← (PartialEquiv.injOn _).ne_iff fm gm]

/-- Locally constant functions are constant on preconnected sets -/
theorem ContMDiffOn.const_of_locally_const [T2Space T] {f : S → T} {s : Set S}
    (fa : ContMDiffOn I I ω f s) {z : S} {a : T} (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  generalize ht : {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, f w = a} = t
  suffices st : s ⊆ t by rw [← ht] at st; exact fun z m ↦ (st m).2.self_of_nhds
  refine p.subset_of_closure_inter_subset ?_ ?_ ?_
  · rw [isOpen_iff_eventually]
    intro z m
    simp only [Set.mem_ofPred_eq, ← ht] at m ⊢
    exact ((o.eventually_mem m.1).and m.2.eventually_nhds).mp (.of_forall fun y h ↦ h)
  · use z; simp only [Set.mem_inter_iff, ← ht]; exact ⟨zs, zs, c⟩
  · intro z m; simp only [Set.mem_inter_iff, mem_closure_iff_frequently] at m
    have aa : ContMDiffAt I I ω (fun _ ↦ a) z := contMDiffAt_const
    cases' (fa.contMDiffAt (o.mem_nhds m.2)).eventually_eq_or_eventually_ne aa with h h
    · rw [← ht]; use m.2, h
    · simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
      have m' := m.1; contrapose m'; simp only [Filter.not_frequently]
      refine h.mp (.of_forall ?_); intro x i
      by_cases xz : x = z; rwa [xz]; specialize i xz; contrapose i
      simp only [← ht] at i ⊢; exact i.2.self_of_nhds

/-- If `S` is locally connected, we don't need the open assumption in
    `ContMDiffOn.const_of_locally_const` -/
theorem ContMDiffOnNhd.const_of_locally_const [LocallyConnectedSpace S] [T2Space T]
    [IsManifold I ω S] [IsManifold I ω T] {f : S → T}
    {s : Set S} (fa : ContMDiffOnNhd I I f s) {z : S} {a : T} (zs : z ∈ s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  rcases local_preconnected_nhdsSet p (isOpen_mAnalyticAt.mem_nhdsSet.mpr fa)
    with ⟨u, uo, su, ua, uc⟩
  exact fun w ws ↦ ContMDiffOn.const_of_locally_const
    (fun _ m ↦ (ua m).contMDiffWithinAt) (su zs) uo uc c w (su ws)

/-- `NontrivialMAnalyticAt f z` implies `f z` is never locally repeated -/
theorem NontrivialMAnalyticAt.eventually_ne [T2Space T] {f : S → T} {z : S}
    (n : NontrivialMAnalyticAt f z) : ∀ᶠ w in 𝓝 z, w ≠ z → f w ≠ f z := by
  have ca : ContMDiffAt I I ω (fun _ ↦ f z) z := contMDiffAt_const
  cases' n.mAnalyticAt.eventually_eq_or_eventually_ne ca with h h
  · have b := h.and_frequently n.nonconst
    simp only [and_not_self_iff, Filter.frequently_false] at b
  · simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at h; convert h

/-- Nontrivially at a point of a preconnected set implies nontriviality throughout the set -/
theorem NontrivialMAnalyticAt.on_preconnected [T2Space T] {f : S → T} {s : Set S} {z : S}
    (fa : ContMDiffOn I I ω f s) (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (n : NontrivialMAnalyticAt f z) : NontrivialMAnalyticOn f s := by
  intro w ws
  replace n := n.nonconst
  refine ⟨fa.contMDiffAt (o.mem_nhds ws), ?_⟩; contrapose n
  simp only [Filter.not_frequently, not_not] at n ⊢; generalize ha : f w = a
  rw [ha] at n
  rw [eventually_nhds_iff]; refine ⟨s, ?_, o, zs⟩
  have c := fa.const_of_locally_const ws o p n
  intro x m; rw [c _ m, c _ zs]

/-- If a `f` is nontrivial at `z`, it is nontrivial near `z` -/
theorem NontrivialMAnalyticAt.eventually [T2Space T] [IsManifold I ω S] [IsManifold I ω T]
    {f : S → T} {z : S} (n : NontrivialMAnalyticAt f z) :
    ∀ᶠ w in 𝓝 z, NontrivialMAnalyticAt f w := by
  have lc : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace ℂ _
  rcases eventually_nhds_iff.mp n.mAnalyticAt.eventually with ⟨s, fa, os, zs⟩
  rcases locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp lc z s (os.mem_nhds zs) with
    ⟨t, ts, ot, zt, ct⟩
  rw [eventually_nhds_iff]; refine ⟨t, ?_, ot, zt⟩
  refine n.on_preconnected (ContMDiffOn.mono ?_ ts) zt ot ct.isPreconnected
  exact fun x m ↦ (fa x m).contMDiffWithinAt

/-- If the derivative isn't zero, we're nontrivial -/
theorem nontrivialMAnalyticAt_of_mfderiv_ne_zero [IsManifold I ω S] [IsManifold I ω T]
    {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z) (d : mfderiv I I f z ≠ 0) :
    NontrivialMAnalyticAt f z := by
  refine ⟨fa, ?_⟩; contrapose d; simp only [Filter.not_frequently, not_not] at d ⊢
  generalize ha : f z = a; rw [ha] at d; apply HasMFDerivAt.mfderiv
  exact (hasMFDerivAt_const a _).congr_of_eventuallyEq d

/-- If `f` and `g` are nontrivial, `f ∘ g` is nontrivial -/
theorem NontrivialMAnalyticAt.comp [T2Space U] {f : T → U} {g : S → T} {z : S}
    (fn : NontrivialMAnalyticAt f (g z)) (gn : NontrivialMAnalyticAt g z) :
    NontrivialMAnalyticAt (fun z ↦ f (g z)) z := by
  use fn.mAnalyticAt.comp _ gn.mAnalyticAt
  convert gn.nonconst.and_eventually (gn.mAnalyticAt.continuousAt.eventually fn.eventually_ne)
  tauto

/-- If `f ∘ g` is nontrivial, and `f, g` are analytic, `f, g` are nontrivial -/
theorem NontrivialMAnalyticAt.anti {f : T → U} {g : S → T} {z : S}
    (h : NontrivialMAnalyticAt (fun z ↦ f (g z)) z) (fa : ContMDiffAt I I ω f (g z))
    (ga : ContMDiffAt I I ω g z) :
    NontrivialMAnalyticAt f (g z) ∧ NontrivialMAnalyticAt g z := by
  replace h := h.nonconst; refine ⟨⟨fa, ?_⟩, ⟨ga, ?_⟩⟩
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact (ga.continuousAt.eventually h).mp (.of_forall fun _ h ↦ h)
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact h.mp (.of_forall fun x h ↦ by rw [h])

/-- `id` is nontrivial -/
-- There's definitely a better way to prove this, but I'm blanking at the moment.
theorem nontrivialMAnalyticAt_id [IsManifold I ω S] (z : S) :
    NontrivialMAnalyticAt (fun w ↦ w) z := by
  use contMDiffAt_id
  rw [Filter.frequently_iff]; intro s sz
  rcases mem_nhds_iff.mp sz with ⟨t, ts, ot, zt⟩
  generalize hu : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t = u
  have uo : IsOpen u := by
    rw [← hu]
    exact (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target _) ot
  have zu : extChartAt I z z ∈ u := by
    simp only [mem_inter_iff, mem_extChartAt_target, true_and, mem_preimage,
      PartialEquiv.left_inv _ (mem_extChartAt_source z), zt, ← hu]
  rcases Metric.isOpen_iff.mp uo _ zu with ⟨r, rp, ru⟩
  generalize ha : extChartAt I z z + r / 2 = a
  have au : a ∈ u := by
    rw [← ha]; apply ru; simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left]
    simp only [norm_div, Complex.norm_real, abs_of_pos rp, Complex.norm_two, Real.norm_eq_abs]
    exact half_lt_self rp
  use (extChartAt I z).symm a
  rw [← hu] at au
  use ts au.2
  rw [← (PartialEquiv.injOn _).ne_iff ((extChartAt I z).map_target au.1) (mem_extChartAt_source z)]
  rw [PartialEquiv.right_inv _ au.1, ← ha]
  simp only [Ne, add_eq_left, div_eq_zero_iff, Complex.ofReal_eq_zero, rp.ne']; norm_num

/-- If `orderAt f z ≠ 0` (`f` has a zero of positive order), then `f` is nontrivial at `z` -/
theorem nontrivialMAnalyticAt_of_order {f : ℂ → ℂ} {z : ℂ} (fa : AnalyticAt ℂ f z)
    (h : orderAt f z ≠ 0) : NontrivialMAnalyticAt f z := by
  use fa.mAnalyticAt I I; contrapose h
  simp only [Filter.not_frequently, not_not] at h ⊢
  have fp : HasFPowerSeriesAt f (constFormalMultilinearSeries ℂ ℂ (f z)) z :=
    hasFPowerSeriesAt_const.congr (Filter.EventuallyEq.symm h)
  simp only [fp.orderAt_unique]; by_contra p0
  have b := FormalMultilinearSeries.apply_order_ne_zero' p0
  simp only [constFormalMultilinearSeries_apply_of_nonzero p0, Ne, not_true] at b

/-- `NontrivialAnalyticOn → NontrivialMAnalyticOn` over `ℂ` -/
theorem NontrivialAnalyticOn.nontrivialMAnalyticOn {f : ℂ → ℂ} {s : Set ℂ}
    (n : NontrivialAnalyticOn f s) : NontrivialMAnalyticOn f s := fun z m ↦
  { mAnalyticAt := (n.analyticOn z m).mAnalyticAt I I
    nonconst := n.nonconst z m }

/-- pow is nontrivial -/
theorem nontrivialMAnalyticAt_pow {d : ℕ} (d0 : d > 0) {z : ℂ} :
    NontrivialMAnalyticAt (fun z ↦ z ^ d) z :=
  (powNontrivial d0).nontrivialMAnalyticOn z (mem_univ _)

/-- Nontriviality is invariant to positive powers -/
theorem NontrivialMAnalyticAt.pow_iff {f : S → ℂ} {z : S} {d : ℕ} (fa : ContMDiffAt I I ω f z)
    (d0 : 0 < d) : NontrivialMAnalyticAt (fun z ↦ f z ^ d) z ↔ NontrivialMAnalyticAt f z := by
  refine ⟨?_, (nontrivialMAnalyticAt_pow d0).comp⟩
  have pa : ContMDiffAt I I ω (fun z ↦ z ^ d) (f z) := (contMDiff_pow d).contMDiffAt
  intro h; refine (NontrivialMAnalyticAt.anti ?_ pa fa).2; exact h

/-- Nontriviality depends only locally on `f` -/
theorem NontrivialMAnalyticAt.congr {f g : S → T} {z : S} (n : NontrivialMAnalyticAt f z)
    (e : f =ᶠ[𝓝 z] g) : NontrivialMAnalyticAt g z := by
  use n.mAnalyticAt.congr_of_eventuallyEq e.symm
  refine n.nonconst.mp (e.mp (.of_forall fun w ew n ↦ ?_))
  rwa [← ew, ← e.self_of_nhds]

section EqOfLocallyEq

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A : Type} [TopologicalSpace A] {J : ModelWithCorners ℂ E A} [J.Boundaryless]
variable {B : Type} [TopologicalSpace B] {K : ModelWithCorners ℂ F B}
variable {M : Type} [TopologicalSpace M] [ChartedSpace A M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace B N]

/-- If two analytic functions are equal locally, they are equal on preconnected sets.

    This is a manifold version of `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
    This is the one higher dimension result in this file, which shows up in that `e`
    requires `f =ᶠ[𝓝 x] g` everywhere near a point rather than only frequent equality
    as would be required in 1D. -/
theorem ContMDiffOnNhd.eq_of_locally_eq [CompleteSpace F] {f g : M → N} [T2Space N]
   {s : Set M} (fa : ContMDiffOnNhd J K f s) (ga : ContMDiffOnNhd J K g s) (sp : IsPreconnected s)
    (e : ∃ x, x ∈ s ∧ f =ᶠ[𝓝 x] g) : f =ᶠ[𝓝ˢ s] g := by
  generalize ht :  {x | f =ᶠ[𝓝 x] g} = t
  suffices h : s ⊆ interior t by
    simp only [subset_interior_iff_mem_nhdsSet, ← Filter.eventually_iff, ← ht] at h
    exact h.mp (.of_forall fun _ e ↦ e.self_of_nhds)
  apply sp.relative_clopen
  · rw [← ht]; exact e
  · intro x ⟨_, xt⟩
    simp only [mem_interior_iff_mem_nhds, ← ht] at xt ⊢
    exact xt.eventually_nhds
  · intro x ⟨xs, xt⟩; rw [mem_closure_iff_frequently] at xt
    have ex' : ∃ᶠ y in 𝓝 x, f y = g y := by
      rw [← ht] at xt; exact xt.mp (.of_forall fun _ e ↦ e.self_of_nhds)
    have ex : f x = g x :=
      tendsto_nhds_unique_of_frequently_eq (fa.continuousAt xs) (ga.continuousAt xs) ex'
    generalize hd : (fun y : E ↦
      extChartAt K (f x) (f ((extChartAt J x).symm y)) -
        extChartAt K (g x) (g ((extChartAt J x).symm y))) = d
    generalize hz : extChartAt J x x = z
    suffices h : d =ᶠ[𝓝 z] 0 by
      simp only [← hz, ← map_extChartAt_nhds_of_boundaryless x, Filter.eventually_map, Filter.EventuallyEq,
        ← ht] at h ⊢
      refine
        h.mp (((isOpen_extChartAt_source x).eventually_mem
        (mem_extChartAt_source (I := J) x)).mp ?_)
      apply ((fa.continuousAt xs).eventually_mem
          ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source (I := K) (f x)))).mp
      apply ((ga.continuousAt xs).eventually_mem ((isOpen_extChartAt_source _).mem_nhds
          (mem_extChartAt_source (I := K) (g x)))).mp
      refine .of_forall fun y gm fm m e ↦ ?_
      rw [← hd, Pi.zero_apply, sub_eq_zero, (extChartAt J x).left_inv m, ex] at e
      rw [ex] at fm; exact (extChartAt K (g x)).injOn fm gm e
    have d0 : ∃ᶠ y in 𝓝 z, d =ᶠ[𝓝 y] 0 := by
      rw [← hz]
      have xt' : ∃ᶠ y in 𝓝 x, (extChartAt J x).symm (extChartAt J x y) ∈ t := by
        apply xt.mp
        apply ((isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := J) x)).mp
        refine .of_forall fun y m e ↦ ?_; rw [(extChartAt J x).left_inv m]; exact e
      apply (Filter.Tendsto.frequently (p := fun y ↦ (extChartAt J x).symm y ∈ t)
          (continuousAt_extChartAt x) xt').mp
      apply ((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target x)).mp
      refine .of_forall fun y m e ↦ ?_; simp only [← ht] at e
      apply ((continuousAt_extChartAt_symm'' m).eventually e).mp
      refine .of_forall fun z e ↦ ?_
      simp only [← hd, Pi.zero_apply, sub_eq_zero, ex, e]
    have da : AnalyticAt ℂ d z := by
      rw [← hd, ← hz]
      exact (mAnalyticAt_iff_of_boundaryless.mp (fa _ xs)).2.sub
        (mAnalyticAt_iff_of_boundaryless.mp (ga _ xs)).2
    clear hd ex ex' xt t e fa ga f g xs hz x sp ht
    -- Forget about manifolds
    rcases da.exists_ball_analyticOnNhd with ⟨r, rp, da⟩
    rcases Filter.frequently_iff.mp d0 (isOpen_ball.mem_nhds (mem_ball_self rp)) with ⟨z0, m0, ze⟩
    refine eventually_nhds_iff.mpr ⟨_, ?_, isOpen_ball, mem_ball_self rp⟩
    exact da.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected m0 ze

end EqOfLocallyEq

end Nontrivial
end
end Ray_Ray_Manifold_Nontrivial

-- ===== Ray.Dynamics.BottcherNearM =====
section Ray_Ray_Dynamics_BottcherNearM
/-!
## Böttcher map near a superattracting fixed point

We define superattracting fixed points of a parameterized analytic map `f : ℂ → S → S` on a 1D
complex manifold S (fixed points of order `d ≥ 2`).  If `a` is such a fixpoint, we get Böttcher
coordinates `s.bottcherNear : ℂ → S → ℂ` that conjugate `f c` to `z ^ d` near `a`

  `s.bottcherNear c (f c z) = s.bottcherNear c z ^ d`

`s.bottcherNear` is defined on `s.near`, an open set close enough to `(c,a)` such that (1) it is
contained within the chart, and (2) the local theory of `BottcherNear.lean` applies.  In particular,
iteration sends `s.near` to `s.near`.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}

/-- `f^[n] z` attracts iff `z` does -/
theorem attracts_shift {f : S → S} {z a : S} (k : ℕ) :
    Attracts f (f^[k] z) a ↔ Attracts f z a := by
  simp only [Attracts, ← Function.iterate_add_apply]
  apply @Filter.tendsto_add_atTop_iff_nat _ fun n ↦ f^[n] z

variable [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]

-- `d` facts
lemma Super.dp (s : Super f d a) : 0 < d := lt_trans (by norm_num) s.d2
lemma Super.dnp (s : Super f d a) {n : ℕ} : 0 < d ^ n := pow_pos s.dp _
lemma Super.d1 (s : Super f d a) : 1 < d := lt_of_lt_of_le (by norm_num) s.d2
lemma Super.d0 (s : Super f d a) : d ≠ 0 := s.dp.ne'

-- Teach `bound` about `Super` and `d`
attribute [bound_forward] Super.dp Super.d1

/-- Iterating at `a` does nothing -/
theorem Super.iter_a (s : Super f d a) (n : ℕ) : (f c)^[n] a = a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply', h, s.f0]

/-- `fl` is analytic -/
theorem Super.fla (s : Super f d a) (c : ℂ) : AnalyticAt ℂ (uncurry s.fl) (c, 0) := by
  rw [analyticAt_iff_mAnalyticAt II I]
  refine ((analyticAt_id.sub analyticAt_const).mAnalyticAt I I).comp _ ?_
  refine (contMDiffAt_extChartAt' ?_).comp _ ?_
  · simp only [s.f0, extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, zero_add,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_toPartialEquiv, Function.comp_apply,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.left_inv,
      OpenPartialHomeomorph.left_inv, mem_chart_source]
  · refine (s.fa _).comp₂ contMDiffAt_fst ?_
    refine ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' ?_)).comp _ ?_
    · simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, zero_add,
        ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_toPartialEquiv, Function.comp_apply,
        PartialEquiv.trans_target, ModelWithCorners.target_eq,
        ModelWithCorners.toPartialEquiv_coe_symm, Set.mem_inter_iff, Set.mem_range_self,
        Set.mem_preimage, ModelWithCorners.left_inv, OpenPartialHomeomorph.map_source,
        mem_chart_source, and_self_iff]
    · exact (analyticAt_snd.add analyticAt_const).mAnalyticAt _ _

/-- `(f c)^[k]` is analytic -/
theorem Super.mAnalyticAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [IsManifold I ω T]
    {g : ℂ × T → ℂ} {h : ℂ × T → S} {p : ℂ × T} {n : ℕ}
    (ga : ContMDiffAt II I ω g p) (ha : ContMDiffAt II I ω h p) :
    ContMDiffAt II I ω (fun p : ℂ × T ↦ (f (g p))^[n] (h p)) p := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact ha
  simp_rw [Function.iterate_succ']; exact (s.fa _).comp₂ ga h

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuous_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {n : ℕ} (gc : Continuous g) (hc : Continuous h) :
    Continuous fun x ↦ (f (g x))^[n] (h x) := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp (gc.prodMk h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuousOn_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {t : Set T} {n : ℕ} (gc : ContinuousOn g t) (hc : ContinuousOn h t) :
    ContinuousOn (fun x ↦ (f (g x))^[n] (h x)) t := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp_continuousOn (gc.prodMk h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuousAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {x : T} {n : ℕ} (gc : ContinuousAt g x) (hc : ContinuousAt h x) :
    ContinuousAt (fun x ↦ (f (g x))^[n] (h x)) x := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact (s.fa _).continuousAt.comp (gc.prodMk h)

/-- `(f c)^[k]` is analytic -/
theorem Super.mAnalytic_iter (s : Super f d a) {k : ℕ} :
    ContMDiff II I ω (fun p : ℂ × S ↦ (f p.1)^[k] p.2) := fun _ ↦
  s.mAnalyticAt_iter contMDiffAt_fst contMDiffAt_snd

/-- `(c,z) ↦ (c, (f c)^[k] z)` is analytic -/
theorem Super.mAnalytic_prod_iter (s : Super f d a) (n : ℕ) :
    ContMDiff II II ω (fun p : ℂ × S ↦ (p.1, (f p.1)^[n] p.2)) := by
  intro p; apply contMDiffAt_fst.prodMk; apply s.mAnalytic_iter

/-- `fl c 0 = 0` -/
theorem Super.fl0 (s : Super f d a) {c : ℂ} : s.fl c 0 = 0 := by
  simp only [Super.fl, _root_.fl, s.f0, Function.comp_apply, zero_add, PartialEquiv.left_inv,
    mem_extChartAt_source, sub_self]

/-- `0` is a critical point for `fl` -/
theorem Super.critical_0 (s : Super f d a) (c : ℂ) : Critical (s.fl c) 0 := by
  simp only [Critical, mfderiv_eq_fderiv, Super.fl]
  have p := (s.fla c).along_snd.leading_approx
  simp only [sub_zero, smul_eq_mul, Super.fl, s.fd, s.fc, mul_one, uncurry] at p
  generalize hg : _root_.fl f a c = g; rw [hg] at p
  have g0 : g 0 = 0 := by rw [← hg]; exact s.fl0
  apply HasFDerivAt.fderiv (f' := (0 : ℂ →L[ℂ] ℂ))
  simp only [hasFDerivAt_iff_isLittleO_nhds_zero, sub_zero, zero_add, g0]
  have od : (fun z : ℂ ↦ z ^ d) =o[𝓝 0] (fun z ↦ z) := by
    rw [Asymptotics.isLittleO_iff]; intro e ep
    apply ((@Metric.isOpen_ball ℂ _ 0 (min 1 e)).eventually_mem (mem_ball_self (by bound))).mp
    refine .of_forall fun z b ↦ ?_
    rw [mem_ball_zero_iff, lt_min_iff] at b
    simp only [norm_pow]
    rw [← Nat.sub_add_cancel s.d2, pow_add, pow_two]
    calc ‖z‖ ^ (d - 2) * (‖z‖ * ‖z‖)
      _ ≤ (1:ℝ) ^ (d - 2) * (‖z‖ * ‖z‖) := by bound
      _ = ‖z‖ * ‖z‖ := by simp only [one_pow, one_mul]
      _ ≤ e * ‖z‖ := by bound
  have p' := (p.trans od).add od
  simp only [sub_add_cancel] at p'
  refine p'.congr_left ?_
  intro z; exact (sub_zero _).symm

/-- `a` is a critical point for `f` -/
theorem Super.critical_a (s : Super f d a) (c : ℂ) : Critical (f c) a := by
  have h := s.critical_0 c
  have e := PartialEquiv.left_inv _ (mem_extChartAt_source (I := I) a)
  contrapose h; simp only [Critical, Super.fl, fl, ← ne_eq] at h ⊢
  simp only [mfderiv_eq_fderiv, _root_.fl, Function.comp_def]
  rw [fderiv_sub_const, ←mfderiv_eq_fderiv]
  apply mderiv_comp_ne_zero' (extChartAt_mderiv_ne_zero' ?_)
  · apply mderiv_comp_ne_zero' (f := f c)
    · rw [zero_add, e]; exact h
    · apply mderiv_comp_ne_zero' (extChartAt_symm_mderiv_ne_zero' ?_)
      · rw [mfderiv_eq_fderiv, fderiv_add_const, ←mfderiv_eq_fderiv]; exact id_mderiv_ne_zero
      · rw [zero_add]; apply mem_extChartAt_target
  · simp only [zero_add, e, s.f0]
    apply mem_extChartAt_source

/-- `f c` is nontrivial at `a` -/
theorem Super.f_nontrivial (s : Super f d a) (c : ℂ) : NontrivialMAnalyticAt (f c) a := by
  refine ⟨(s.fa _).along_snd, ?_⟩; simp only [s.f0]
  have n : ∃ᶠ w in 𝓝 (0 : ℂ), s.fl c w ≠ 0 := by
    have e := (nontrivialMAnalyticAt_of_order (s.fla c).along_snd ?_).nonconst
    · simp only [s.fl0, uncurry] at e; exact e
    · simp only [Super.fl, s.fd, uncurry]; exact s.d0
  contrapose n
  simp only [Filter.not_frequently, not_not, Super.fl, fl] at n ⊢
  have gc : ContinuousAt (fun x ↦ (extChartAt I a).symm (x + extChartAt I a a)) 0 := by
    refine (continuousAt_extChartAt_symm a).comp_of_eq ?_ (by simp only [zero_add])
    exact continuousAt_id.add continuousAt_const
  simp only [ContinuousAt, zero_add, PartialEquiv.left_inv _ (mem_extChartAt_source _)] at gc
  refine (gc.eventually n).mp (.of_forall ?_)
  intro x h; simp only [_root_.fl, Function.comp_def, h, sub_self]

/-- Close enough to `a`, `f c z ∈ (ext_chart_at I a).source` -/
theorem Super.stays_in_chart (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
  apply ContinuousAt.eventually_mem_nhd
  exact (s.fa.continuous.comp continuous_id).continuousAt
  simp only [s.f0, extChartAt_source_mem_nhds a]

/-- There is a open set around the attractor in `ext_chart I a` where things are nice -/
theorem Super.fr_prop (s : Super f d a) (c : ℂ) :
    ∃ r, r > 0 ∧ AnalyticOnNhd ℂ (uncurry s.fl) (ball (c, 0) r) ∧
      ∀ p : ℂ × S, p ∈ (extChartAt II (c, a)).source →
        extChartAt II (c, a) p ∈ ball (extChartAt II (c, a) (c, a)) r →
          f p.1 p.2 ∈ (extChartAt I a).source := by
  rcases(s.fla c).exists_ball_analyticOnNhd with ⟨r0, r0p, fla⟩
  rcases eventually_nhds_iff.mp (s.stays_in_chart c) with ⟨t, tp, ot, ta⟩
  set ch := extChartAt II (c, a)
  set s := ch.target ∩ ch.symm ⁻¹' t
  have os : IsOpen s :=
    (continuousOn_extChartAt_symm (c, a)).isOpen_inter_preimage (isOpen_extChartAt_target (c, a)) ot
  have m : ch (c, a) ∈ s := by
    apply Set.mem_inter (mem_extChartAt_target _)
    rw [Set.mem_preimage, ch.left_inv (mem_extChartAt_source _)]
    exact ta
  rcases Metric.isOpen_iff.mp os (ch (c, a)) m with ⟨r1, r1p, rs⟩
  · use min r0 r1, by bound
    use fla.mono (Metric.ball_subset_ball (by bound))
    intro p ps pr; apply tp p
    rw [← ch.left_inv ps, ← Set.mem_preimage]
    exact Set.mem_of_mem_inter_right (rs (Metric.ball_subset_ball (by bound) pr))

/-- A radius around `(c,0)` on which `f` and `fl` are nice -/
def Super.fr (s : Super f d a) (c : ℂ) : ℝ :=
  choose (s.fr_prop c)

theorem Super.frp (s : Super f d a) (c : ℂ) : 0 < s.fr c :=
  (choose_spec (s.fr_prop c)).1

theorem Super.fla_on (s : Super f d a) (c : ℂ) :
    AnalyticOnNhd ℂ (uncurry s.fl) (ball (c, 0) (s.fr c)) :=
  (choose_spec (s.fr_prop c)).2.1

theorem Super.fr_stays (s : Super f d a) (c : ℂ) (p : ℂ × S)
    (ps : p ∈ (extChartAt II (c, a)).source)
    (pr : extChartAt II (c, a) p ∈ ball (extChartAt II (c, a) (c, a)) (s.fr c)) :
    f p.1 p.2 ∈ (extChartAt I a).source :=
  (choose_spec (s.fr_prop c)).2.2 p ps pr

/-- We'll stay within this set when constructing `s.nice` -/
def Super.fls (s : Super f d a) : Set (ℂ × ℂ) :=
  ⋃ c, ball (c, (0 : ℂ)) (s.fr c)

lemma Super.fls_open (s : Super f d a) : IsOpen s.fls :=
  isOpen_iUnion fun _ ↦ isOpen_ball

/-- `b ∈ ball 0 r → (b,0) ∈ ball 0 r` -/
theorem prod_zero_mem_ball {c b : ℂ} {r : ℝ} (m : b ∈ ball c r) :
    (b, (0 : ℂ)) ∈ ball (c, (0 : ℂ)) r := by
  simp only [Metric.mem_ball] at m; simpa only [Metric.mem_ball, dist_prod_same_right]

/-- `Super → SuperAtC` in charts -/
theorem Super.superAtC (s : Super f d a) : SuperAtC s.fl d univ :=
  { o := isOpen_univ
    fa := fun {_} _ ↦ s.fla _
    s := fun {c} _ ↦
      { d2 := s.d2
        fd := s.fd _
        fc := s.fc _
        fa0 := (s.fla c).along_snd } }

/-- `Super → SuperNearC` in charts for a suitable set -/
theorem Super.exists_superNearC (s : Super f d a) :
    ∃ t, t ⊆ s.fls ∧ SuperNearC s.fl d univ t (1 / 2) (1 / 4) := by
  refine s.superAtC.superNearC' s.fls_open fun c _ ↦ ?_
  rw [Super.fls, Set.mem_iUnion]; use c; exact mem_ball_self (s.frp c)

/-- The set of points on which `bottcherNear` is defined, in charts -/
def Super.near' (s : Super f d a) : Set (ℂ × ℂ) :=
  choose s.exists_superNearC

theorem Super.near_subset' (s : Super f d a) : s.near' ⊆ s.fls :=
  (choose_spec s.exists_superNearC).1

/-- The set on which `bottcherNear` is defined, where we are both within the chart and close
    enough to `a` to satisfy the smallness conditions needed for `SuperNearC` -/
def Super.near (s : Super f d a) : Set (ℂ × S) :=
  (extChartAt II ((0 : ℂ), a)).source ∩
    extChartAt II ((0 : ℂ), a) ⁻¹' {p : ℂ × ℂ | (p.1, p.2 - extChartAt I a a) ∈ s.near'}

theorem Super.superNearC (s : Super f d a) :
    SuperNearC s.fl d univ s.near' (1 / 2) (1 / 4) :=
  (choose_spec s.exists_superNearC).2

theorem Super.isOpen_near (s : Super f d a) : IsOpen s.near := by
  apply (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
  exact IsOpen.preimage (continuous_fst.prodMk (continuous_snd.sub continuous_const))
    s.superNearC.o

/-- `(c,a)` is near -/
@[simp] theorem Super.mem_near (s : Super f d a) (c : ℂ) : (c, a) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and,
    Set.mem_preimage, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, Set.mem_ofPred_eq, sub_self]
  exact (s.superNearC.s (Set.mem_univ _)).t0

/-- `s.near` stays within the chart -/
theorem Super.near_subset_chart (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) :
    z ∈ (extChartAt I a).source := by
  have h := Set.mem_of_mem_inter_left m
  simp only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod_eq] at h
  exact h.2

theorem Super.mem_near_to_near' (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    (p.1, extChartAt I a p.2 - extChartAt I a a) ∈ s.near' := by
  have h := Set.mem_of_mem_inter_right m
  simp only [Set.mem_preimage, extChartAt_prod, PartialEquiv.prod_coe, extChartAt_eq_refl,
    PartialEquiv.refl_coe, id] at h
  exact h

/-- Once we're in `s.near`, we stay there -/
theorem Super.stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) :
    (c, f c z) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and, Set.mem_preimage,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, Set.mem_ofPred_eq] at m ⊢
  rcases mem_iUnion.mp (s.near_subset' m.2) with ⟨b, mb⟩
  simp only [mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at mb
  constructor
  · apply s.fr_stays b (c, z)
    simp only [m.1, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, extChartAt_eq_refl,
      PartialEquiv.refl_source, Set.mem_univ, true_and]
    simp only [mb.1, mb.2, extChartAt_prod, extChartAt_eq_refl, true_and, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe, id, mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub,
      Prod.snd_sub]
  · have h := (s.superNearC.s (Set.mem_univ c)).ft m.2
    simp only [Super.fl, _root_.fl, Function.comp_def, sub_add_cancel,
      PartialEquiv.left_inv _ m.1] at h
    exact h

/-- Once we're in `s.near`, we stay there forever -/
theorem Super.iter_stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near)
    (n : ℕ) : (c, (f c)^[n] z) ∈ s.near := by
  induction' n with n h; simp only [Function.iterate_zero, id, m]
  simp only [Nat.add_succ, Function.iterate_succ', s.stays_near h, Function.comp_def]

/-- More iterations stay in `s.near` -/
theorem Super.iter_stays_near' (s : Super f d a) {a b : ℕ} (m : (c, (f c)^[a] z) ∈ s.near)
    (ab : a ≤ b) : (c, (f c)^[b] z) ∈ s.near := by
  rw [← Nat.sub_add_cancel ab, Function.iterate_add_apply]; exact s.iter_stays_near m _

/-- If `z` attracts, it eventually reaches `s.near` -/
theorem Super.reaches_near (s : Super f d a) {z : S} (a : Attracts (f c) z a) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  rw [Attracts, Filter.tendsto_iff_forall_eventually_mem] at a
  have e := a {z | (c, z) ∈ s.near} ?_; exact e
  apply IsOpen.mem_nhds; apply IsOpen.snd_preimage s.isOpen_near; exact s.mem_near c

/-- If `z` reaches `s.near`, it attracts to `a` -/
theorem Super.attracts (s : Super f d a) {n : ℕ} (r : (c, (f c)^[n] z) ∈ s.near) :
    Attracts (f c) z a := by
  have m := s.mem_near_to_near' r
  have t := iterates_tendsto (s.superNearC.s (Set.mem_univ c)) m
  generalize hg : (fun x : ℂ ↦ (extChartAt I a).symm (x + extChartAt I a a)) = g
  have gc : ContinuousAt g 0 := by
    rw [← hg]
    refine (continuousAt_extChartAt_symm'' ?_).comp
      (continuous_id.add continuous_const).continuousAt
    simp only [zero_add]; exact mem_extChartAt_target a
  have g0 : g 0 = a := by
    simp only [← hg]; simp only [zero_add]; exact PartialEquiv.left_inv _ (mem_extChartAt_source _)
  have h := gc.tendsto.comp t; clear t gc m
  simp only [Function.comp_def, g0] at h
  rw [← attracts_shift n]
  refine Filter.Tendsto.congr ?_ h; clear h
  intro k; simp only [← hg]; induction' k with k h
  simp only [Function.iterate_zero_apply]; rw [sub_add_cancel]
  exact PartialEquiv.left_inv _ (s.near_subset_chart r)
  simp only [Function.iterate_succ_apply']
  generalize hx : (s.fl c)^[k] (extChartAt I a ((f c)^[n] z) - extChartAt I a a) = x; rw [hx] at h
  simp only [Super.fl, _root_.fl, Function.comp_def, sub_add_cancel, h,
    ←Function.iterate_succ_apply' (f c)]
  apply PartialEquiv.left_inv _ (s.near_subset_chart (s.iter_stays_near r _))

/-- The basin is all points that reach `s.near` -/
lemma Super.basin_iff_near (s : Super f d a) {p : ℂ × S} :
    p ∈ s.basin ↔ ∃ n, (p.1, (f p.1)^[n] p.2) ∈ s.near := by
  constructor
  · intro m
    simp only [basin, mem_ofPred_eq] at m
    have e : ∀ᶠ n in atTop, (f p.1)^[n] p.2 ∈ {x : S | (p.1, x) ∈ s.near} :=
      m.eventually_mem ((s.isOpen_near.snd_preimage p.1).mem_nhds (by simp))
    exact e.exists
  · intro ⟨n,  m⟩
    exact s.attracts m

/-- Anything in `s.basin` attracts -/
theorem Super.basin_attracts (s : Super f d a) (m : (c, z) ∈ s.basin) :
    Attracts (f c) z a := by
  rcases s.basin_iff_near.mp m with ⟨n, m⟩
  exact s.attracts m

theorem Super.isOpen_preimage (s : Super f d a) (n : ℕ) :
    IsOpen {p : ℂ × S | (p.1, (f p.1)^[n] p.2) ∈ s.near} :=
  IsOpen.preimage (continuous_fst.prodMk (s.continuous_iter continuous_fst continuous_snd))
    s.isOpen_near

/-- `s.basin` is open -/
theorem Super.isOpen_basin (s : Super f d a) : IsOpen s.basin := by
  have e : s.basin = ⋃ n, {p : ℂ × S | (p.1, (f p.1)^[n] p.2) ∈ s.near} := by
    ext p; simp [s.basin_iff_near]
  rw [e]
  exact isOpen_iUnion fun n ↦ s.isOpen_preimage n

/-- Anything in `s.basin` is eventually in `s.near` -/
theorem Super.basin_stays (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  rcases s.basin_iff_near.mp m with ⟨n, m⟩
  rw [Filter.eventually_atTop]; use n; intro k kn
  rw [← Nat.sub_add_cancel kn, Function.iterate_add_apply]
  exact s.iter_stays_near m _

/-- `s.basin` is exactly the set of attracting points -/
theorem Super.basin_iff_attracts (s : Super f d a) :
    (c, z) ∈ s.basin ↔ Attracts (f c) z a := by
  constructor
  · exact s.basin_attracts
  · intro h
    rcases tendsto_atTop_nhds.mp h {z | (c, z) ∈ s.near} (s.mem_near c)
      (s.isOpen_near.snd_preimage c) with ⟨n, h⟩
    simp only [s.basin_iff_near]
    exact ⟨n, h _ (le_refl _)⟩

/-- `f` acting on and returning pairs -/
def Super.fp (_ : Super f d a) : ℂ × S → ℂ × S := fun p : ℂ × S ↦ (p.1, f p.1 p.2)

/-- `s.fp` is analytic -/
theorem Super.fpa (s : Super f d a) : ContMDiff II II ω s.fp := fun _ ↦
  contMDiffAt_fst.prodMk (s.fa _)

theorem Super.fp1 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).1 = p.1 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · simp only [Function.iterate_succ_apply', h, fp]

theorem Super.fp2 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).2 = (f p.1)^[n] p.2 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · simp only [Function.iterate_succ_apply', s.fp1 n p, h, fp]

/-- `s.bottcherNear` is analytic -/
theorem Super.bottcherNear_mAnalytic (s : Super f d a) :
    ContMDiffOn II I ω (uncurry s.bottcherNear) s.near := by
  intro p m
  have e : uncurry s.bottcherNear =
      (fun p : ℂ × ℂ ↦ _root_.bottcherNear (s.fl p.1) d p.2) ∘ fun p : ℂ × S ↦
        (p.1, extChartAt I a p.2 - extChartAt I a a) :=
    rfl
  rw [e]; clear e
  have h1 := (bottcherNear_analytic s.superNearC _ (s.mem_near_to_near' m)).mAnalyticAt II I
  have h2 : ContMDiffAt II II ω (fun p : ℂ × S ↦
      (p.1, extChartAt I a p.2 - extChartAt I a a)) p := by
    apply contMDiffAt_fst.prodMk; apply ContMDiffAt.sub
    exact (contMDiffAt_extChartAt' (extChartAt_source I a ▸ (s.near_subset_chart m))).comp _ contMDiffAt_snd
    exact contMDiffAt_const
  exact (h1.comp_of_eq h2 rfl).contMDiffWithinAt

/-- `s.bottcherNear` is analytic -/
theorem Super.bottcherNear_mAnalytic' (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    ContMDiffAt II I ω (uncurry s.bottcherNear) p :=
  s.bottcherNear_mAnalytic.contMDiffAt (s.isOpen_near.mem_nhds m)

theorem Super.bottcherNearIter_mAnalytic (s : Super f d a) {n : ℕ}
    (r : (c, (f c)^[n] z) ∈ s.near) :
    ContMDiffAt II I ω (uncurry (s.bottcherNearIter n)) (c, z) := by
  -- For this reason this doesn't infer unless we give tons of type hints
  apply ContMDiffAt.comp (g := uncurry (s.bottcherNear)) (f := fun p ↦ (p.1, (f p.1)^[n] p.2))
    (x := (c, z)) (I := II) (I' := II) (I'' := I)
  · exact s.bottcherNear_mAnalytic' r
  · exact contMDiffAt_fst.prodMk (s.mAnalytic_iter _)

/-- `s.bottcherNear` satisfies the defining equation -/
theorem Super.bottcherNear_eqn (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c (f c z) = s.bottcherNear c z ^ d := by
  simp only [Super.bottcherNear]
  have e : extChartAt I a (f c z) - extChartAt I a a =
      s.fl c (extChartAt I a z - extChartAt I a a) := by
    simp only [Function.comp_def, Super.fl, _root_.fl, sub_add_cancel,
      PartialEquiv.left_inv _ (s.near_subset_chart m)]
  rw [e, _root_.bottcherNear_eqn (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)]

/-- `s.bottcherNear_eqn` iterated -/
theorem Super.bottcherNear_eqn_iter (s : Super f d a) (m : (c, z) ∈ s.near) {n : ℕ} :
    s.bottcherNear c ((f c)^[n] z) = s.bottcherNear c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcherNear_eqn (s.iter_stays_near m n), h, ←
    pow_mul, ← pow_succ]

/-- The defining equation in terms of `s.bottcherNearp` and `s.fp` -/
theorem Super.bottcherNearp_eqn (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    s.bottcherNearp (s.fp p) = s.bottcherNearp p ^ d := by
  rcases p with ⟨c, z⟩
  exact s.bottcherNear_eqn m

/-- `abs (s.bottcherNear c z) < 1` -/
theorem Super.bottcherNear_lt_one (s : Super f d a) (m : (c, z) ∈ s.near) :
    ‖s.bottcherNear c z‖ < 1 := by
  simp only [Super.bottcherNear]
  exact _root_.bottcherNear_lt_one (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)

/-- `s.bottcherNear = 0` only at `a` -/
theorem Super.bottcherNear_eq_zero (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c z = 0 ↔ z = a := by
  simp only [Super.bottcherNear]; constructor
  · intro za; contrapose za
    apply bottcherNear_ne_zero (s.superNearC.s (Set.mem_univ _)) (s.mem_near_to_near' m)
    simp only [sub_ne_zero]
    exact (extChartAt I a).injOn.ne (s.near_subset_chart m) (mem_extChartAt_source a) za
  · intro za; simp only [za, sub_self, bottcherNear_zero]

/-- `s.bottcherNear c a = 0` -/
theorem Super.bottcherNear_a (s : Super f d a) : s.bottcherNear c a = 0 := by
  simp only [Super.bottcherNear, sub_self, bottcherNear_zero]

/-- `s.bottcherNear' ≠ 0` at `0` -/
theorem Super.bottcherNear_mfderiv_ne_zero (s : Super f d a) (c : ℂ) :
    mfderiv I I (s.bottcherNear c) a ≠ 0 := by
  apply mderiv_comp_ne_zero' (f := _root_.bottcherNear (s.fl c) d)
  · simp only [sub_self, mfderiv_eq_fderiv,
      (_root_.bottcherNear_monic (s.superNearC.s (Set.mem_univ c))).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.smulRight_ne_zero ContinuousLinearMap.one_ne_zero (by norm_num)
  · have u : (fun z : S ↦ extChartAt I a z - extChartAt I a a) =
        extChartAt I a - fun _ : S ↦ extChartAt I a a := rfl
    rw [u, mfderiv_sub, mfderiv_const]
    · intro h
      apply extChartAt_mderiv_ne_zero a
      apply ContinuousLinearMap.ext
      intro v
      exact (sub_zero _).symm.trans (ContinuousLinearMap.ext_iff.mp h v)
    · exact (contMDiffAt_extChartAt' (mem_chart_source _ a)).mdifferentiableAt one_ne_zero
    · apply mdifferentiableAt_const

/-- `s.bottcherNear` is invertible near any `(c,a)` -/
theorem Super.bottcherNear_has_inv (s : Super f d a) (c : ℂ) :
    ∃ bi : ℂ → ℂ → S,
      ContMDiffAt II I ω (uncurry bi) (c, 0) ∧
        (∀ᶠ p : ℂ × S in 𝓝 (c, a), bi p.1 (s.bottcherNear p.1 p.2) = p.2) ∧
          ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear p.1 (bi p.1 p.2) = p.2 := by
  have h := complex_inverse_fun (s.bottcherNear_mAnalytic' (s.mem_near c))
      (s.bottcherNear_mfderiv_ne_zero c)
  simp only [s.bottcherNear_a] at h; exact h

/-- `f` is locally noncritical near (but not at) `a`.
    This is a depressingly long proof for a very simple conceptual argument. -/
theorem Super.f_noncritical_near_a (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), Critical (f p.1) p.2 ↔ p.2 = a := by
  have t : ContinuousAt (fun p : ℂ × S ↦ (p.1, extChartAt I a p.2 - extChartAt I a a)) (c, a) := by
    refine continuousAt_fst.prodMk (ContinuousAt.sub ?_ continuousAt_const)
    exact (continuousAt_extChartAt a).comp_of_eq continuousAt_snd rfl
  simp only [ContinuousAt, sub_self] at t
  apply (inChart_critical (s.fa (c, a))).mp
  apply (t.eventually (df_ne_zero s.superNearC (Set.mem_univ c))).mp
  have am := mem_extChartAt_source (I := I) a
  have em := ((isOpen_extChartAt_source a).eventually_mem am).prod_inr (𝓝 c)
  simp only [← nhds_prod_eq] at em; apply em.mp
  have ezm : ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
    refine (s.fa _).continuousAt.eventually_mem (extChartAt_source_mem_nhds' ?_)
    simp only [uncurry, s.f0, mem_extChartAt_source a]
  apply ezm.mp
  refine .of_forall ?_; clear t em
  intro ⟨e, z⟩ ezm zm d0 m0; simp only at ezm zm d0 m0 ⊢
  simp only [Super.fl, fl, sub_eq_zero, (PartialEquiv.injOn _).eq_iff zm am] at d0
  simp only [Critical, m0, ← d0]
  unfold inChart
  clear m0 d0
  generalize hg : (fun w ↦ extChartAt I (f c a) (f e ((extChartAt I a).symm w))) = g
  have hg' : extChartAt I a ∘ f e ∘ (extChartAt I a).symm = g := by
    rw [← hg]; simp only [Function.comp_def, s.f0]
  rw [_root_.fl, hg']; clear hg'; rw [Iff.comm]
  have dg : DifferentiableAt ℂ g (extChartAt I a z) := by
    rw [← hg]
    apply AnalyticAt.differentiableAt
    apply ContMDiffAt.analyticAt I I
    simp only [s.f0]
    apply (contMDiffAt_extChartAt' _).comp; apply (s.fa _).along_snd.comp
    exact (contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' (PartialEquiv.map_source _ zm))
    simp only [PartialEquiv.left_inv _ zm]; exact extChartAt_source I a ▸ ezm
  have d0 : ∀ z, DifferentiableAt ℂ (fun z ↦ z - extChartAt I a a) z := fun z ↦
    differentiableAt_id.sub (differentiableAt_const _)
  have d1 : DifferentiableAt ℂ (g ∘ fun z : ℂ ↦ z + extChartAt I a a)
      (extChartAt I a z - extChartAt I a a) := by
    apply DifferentiableAt.comp; simp only [sub_add_cancel, dg]
    exact differentiableAt_id.add (differentiableAt_const _)
  simp only [deriv_comp _ (d0 _) d1, deriv_sub_const, deriv_id'', one_mul]
  rw [deriv_comp _ _ _]
  · simp only [deriv_add_const, deriv_id'', mul_one, sub_add_cancel]
  · simp only [sub_add_cancel, dg]
  · exact differentiableAt_id.add (differentiableAt_const _)

/-- Critical points that are not `a` are closed, because `a` is an isolated critical point in `z` -/
theorem Super.isClosed_critical_not_a (s : Super f d a) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2 ∧ p.2 ≠ a} := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m
  by_cases za : z = a
  · rw [za]; refine (s.f_noncritical_near_a c).mp (.of_forall ?_); intro ⟨e, w⟩ h
    simp only [mem_compl_iff, mem_ofPred, not_and, not_not] at h ⊢; exact h.1
  · have o := isOpen_iff_eventually.mp (isOpen_noncritical s.fa)
    simp only [za, mem_compl_iff, mem_ofPred, not_and, not_not, imp_false] at m o ⊢
    refine (o (c, z) m).mp (.of_forall ?_); intro ⟨e, w⟩ a b; exfalso; exact a b

/-- If `z ∈ s.basin`, iterating enough takes us to a noncritical point of `s.bottcherNear` -/
theorem Super.eventually_noncritical (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0 :=
  (s.basin_attracts m).eventually
    (mfderiv_ne_zero_eventually (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c))

/-- `s.bottcherNearIter` is noncritical given noncriticality of the two parts -/
theorem Super.bottcherNearIter_mfderiv_ne_zero (s : Super f d a)
    (b0 : mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0) (f0 : ¬Precritical (f c) z) :
    mfderiv I I (s.bottcherNearIter n c) z ≠ 0 := by
  apply mderiv_comp_ne_zero' b0; contrapose f0
  exact critical_iter s.fa.along_snd f0

/-- `f c^[n]` is nontrivial at `a` -/
theorem Super.iter_nontrivial_a [T2Space S] (s : Super f d a) :
    NontrivialMAnalyticAt (fun z ↦ (f c)^[n] z) a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]; apply nontrivialMAnalyticAt_id
  simp only [Function.iterate_succ_apply']; refine NontrivialMAnalyticAt.comp ?_ h
  simp only [s.iter_a]; exact s.f_nontrivial c

/-- `s.bottcherNearIter` is nontrivial at `a` -/
theorem Super.bottcherNearIter_nontrivial_a [T2Space S] (s : Super f d a) :
    NontrivialMAnalyticAt (s.bottcherNearIter n c) a :=
  haveI b : NontrivialMAnalyticAt (s.bottcherNear c) ((f c)^[n] a) := by
    simp only [s.iter_a]
    exact nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c)
  b.comp s.iter_nontrivial_a

end
end Ray_Ray_Dynamics_BottcherNearM


