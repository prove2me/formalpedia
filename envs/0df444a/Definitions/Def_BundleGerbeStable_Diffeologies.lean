-- Prove2me | Definitions.Def_BundleGerbeStable_Diffeologies
-- name    : BundleGerbeStable_Diffeologies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:29.830665+00:00
-- url     : https://prove2.me/theorems/b8690ce2-c717-4ac1-9a50-a9a26b344a95
-- title:
--   Induced, product and discrete diffeologies; the manifold diffeology on $M$
-- statement:
--   A **diffeology** on a set declares which maps from Euclidean spaces are smooth (its *plots*). Murray and Stevenson work in a category of spaces "deduced from context" that includes finite-dimensional manifolds, infinite-dimensional manifolds and differentiable spaces; diffeological spaces contain all of these. This file supplies the constructions the mission needs:
--
--   1. the **induced diffeology** of a map $f : X \to Y$, whose plots are the $p$ with $f\circ p$ a plot, used for subspaces such as fibre products and open subsets of $M$;
--   2. the **product diffeology**, whose plots are pairs of plots;
--   3. the **discrete diffeology**, whose plots are the locally constant maps;
--   4. the diffeology of $\mathbb C$ as a real normed space, and that of $\mathbb C^\times$ induced from $\mathbb C$;
--   5. the **manifold diffeology**: on a smooth manifold $M$ the plots are the $C^\infty$ maps $\mathbb R^n \to M$. The class `IsManifoldDiffeology E M` says the diffeology of $M$ is this one.
--
--   These are the smooth structures on which every later definition rests.
--
--   **Formalization Note.** Mathlib's `Geometry/Diffeology/Basic.lean` has `DiffeologicalSpace`, `DSmooth` and `NormedSpace.toDiffeology`, but no subspace, product or discrete diffeology. Small lemmas (smoothness of projections, pairs, inversion and multiplication in $\mathbb C^\times$) are included for use in the proofs of later definitions.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.2 (the category of spaces)

import Mathlib

open Diffeology ContDiff Manifold

namespace BundleGerbeStable

/-- The diffeology induced by a map `f : X → Y`: a plot of `X` is a map whose composite with `f` is a
plot of `Y`. Used for subspaces and for `ℂˣ ⊂ ℂ` (Murray, Stevenson, *Bundle gerbes: stable
isomorphism and local theory*, arXiv:math/9908135v1, §2, p.2).

**Formalization Note.** Mathlib's `Geometry/Diffeology/Basic.lean` has no induced, subspace, product
or discrete diffeology, so they are supplied here. The paper says (p.2) that "the category can be
deduced from context" and names finite-dimensional manifolds, infinite-dimensional manifolds and
differentiable spaces; diffeological spaces contain all of them. -/
@[instance_reducible]
def inducedDiffeology {X Y : Type*} [DiffeologicalSpace Y] (f : X → Y) : DiffeologicalSpace X where
  plots _ := {p | IsPlot (f ∘ p)}
  constant_plots _ := isPlot_const
  plot_reparam hp hf := isPlot_reparam hp hf
  locality hp := DiffeologicalSpace.locality fun x ↦
    let ⟨u, hu, hxu, h⟩ := hp x
    ⟨u, hu, hxu, fun hfu hf ↦ h hfu hf⟩

/-- The subspace diffeology, used for fibre products and for open subsets of the base. -/
instance subtypeDiffeology {X : Type*} [DiffeologicalSpace X] (q : X → Prop) :
    DiffeologicalSpace (Subtype q) :=
  inducedDiffeology Subtype.val

/-- The product diffeology: a plot of `X × Y` is a pair of plots. -/
instance prodDiffeology {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] :
    DiffeologicalSpace (X × Y) where
  plots _ := {p | IsPlot (Prod.fst ∘ p) ∧ IsPlot (Prod.snd ∘ p)}
  constant_plots _ := ⟨isPlot_const, isPlot_const⟩
  plot_reparam hp hf := ⟨isPlot_reparam hp.1 hf, isPlot_reparam hp.2 hf⟩
  locality hp :=
    ⟨DiffeologicalSpace.locality fun x ↦
        let ⟨u, hu, hxu, h⟩ := hp x
        ⟨u, hu, hxu, fun hfu hf ↦ (h hfu hf).1⟩,
      DiffeologicalSpace.locality fun x ↦
        let ⟨u, hu, hxu, h⟩ := hp x
        ⟨u, hu, hxu, fun hfu hf ↦ (h hfu hf).2⟩⟩

/-- The discrete diffeology: the plots are exactly the locally constant maps. It is a definition,
not an instance: it is used only for the index set of the nerve of a cover. -/
@[instance_reducible]
def discreteDiffeology (I : Type*) : DiffeologicalSpace I :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ∀ x ∈ u, ∀ᶠ y in nhds x, p y = p x
    isPlotOn_congr := fun {_ u} hu {p q} h ↦ by
      refine ⟨fun hp x hx ↦ ?_, fun hp x hx ↦ ?_⟩
      · filter_upwards [hp x hx, hu.mem_nhds hx] with y hy hyu
        rw [← h hyu, ← h hx, hy]
      · filter_upwards [hp x hx, hu.mem_nhds hx] with y hy hyu
        rw [h hyu, h hx, hy]
    isPlot_const := fun _ _ _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl
    isPlotOn_reparam := fun {_ _ _ v _} hv {p f} h hp hf x hx ↦ by
      have hc : Filter.Tendsto f (nhds x) (nhds (f x)) :=
        (hf.continuousOn.continuousAt (hv.mem_nhds hx)).tendsto
      exact hc.eventually (hp (f x) (h hx))
    locality := fun _ _ h x hx ↦
      let ⟨_, _, hxv, hv'⟩ := h x hx
      hv' x hxv }

/-- `ℂ` carries the diffeology of its underlying finite-dimensional real normed space. -/
noncomputable instance complexDiffeology : DiffeologicalSpace ℂ := NormedSpace.toDiffeology ℂ

/-- `ℂˣ` carries the diffeology induced from `ℂ`: a plot is a map whose values, read in `ℂ`, are
smooth. -/
noncomputable instance unitsDiffeology : DiffeologicalSpace ℂˣ := inducedDiffeology (Units.val : ℂˣ → ℂ)

/-- The diffeology of `M` is that of a smooth manifold modelled on `E`: the plots
`EuclideanSpace ℝ (Fin n) → M` are exactly the `C^∞` maps. This is the analogue for manifolds of
Mathlib's `IsContDiffCompatible`; it determines the diffeology, and `manifoldDiffeology` shows that
such a diffeology exists. -/
class IsManifoldDiffeology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [DiffeologicalSpace M] : Prop where
  isPlot_iff {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → M} :
    IsPlot p ↔ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p

/-- The manifold diffeology: the plots are the `C^∞` maps from Euclidean spaces. -/
@[instance_reducible]
def manifoldDiffeology (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : DiffeologicalSpace M :=
  .ofCorePlotsOn {
    isPlotOn := fun {n u} _ p ↦ ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contMDiffOn_congr h
    isPlot := fun {n} p ↦ ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ ↦ contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf.contMDiffOn h.subset_preimage
    locality := fun _ _ h x hxu ↦
      let ⟨_, hv, hxv, hv'⟩ := h x hxu
      ((hv' x hxv).contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt }

section Lemmas

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

theorem dSmooth_fst : DSmooth (Prod.fst : X × Y → X) := fun _ _ hp ↦ hp.1

theorem dSmooth_snd : DSmooth (Prod.snd : X × Y → Y) := fun _ _ hp ↦ hp.2

theorem DSmooth.prodMk' {f : Z → X} {g : Z → Y} (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth (fun z ↦ (f z, g z)) := fun n p hp ↦ ⟨hf n p hp, hg n p hp⟩

theorem dSmooth_subtype_val {q : X → Prop} : DSmooth (Subtype.val : Subtype q → X) :=
  fun _ _ hp ↦ hp

theorem DSmooth.subtype_mk' {q : X → Prop} {f : Z → X} (hf : DSmooth f) (h : ∀ z, q (f z)) :
    DSmooth (fun z ↦ (⟨f z, h z⟩ : Subtype q)) := fun n p hp ↦ hf n p hp

theorem dSmooth_units_val : DSmooth (Units.val : ℂˣ → ℂ) := fun _ _ hp ↦ hp

/-- Inversion on `ℂˣ` is smooth. -/
theorem dSmooth_units_inv : DSmooth (fun z : ℂˣ ↦ z⁻¹) := fun n p hp ↦ by
  have hp' : ContDiff ℝ ∞ (fun x ↦ ((p x : ℂˣ) : ℂ)) := hp
  have : ContDiff ℝ ∞ (fun x ↦ ((p x : ℂˣ) : ℂ)⁻¹) :=
    hp'.inv fun x ↦ (p x).ne_zero
  show ContDiff ℝ ∞ (fun x ↦ (((p x)⁻¹ : ℂˣ) : ℂ))
  simpa [Units.val_inv_eq_inv_val] using this

/-- Multiplication on `ℂˣ` is smooth. -/
theorem dSmooth_units_mul : DSmooth (fun z : ℂˣ × ℂˣ ↦ z.1 * z.2) := fun n p hp ↦ by
  have h₁ : ContDiff ℝ ∞ (fun x ↦ (((p x).1 : ℂˣ) : ℂ)) := hp.1
  have h₂ : ContDiff ℝ ∞ (fun x ↦ (((p x).2 : ℂˣ) : ℂ)) := hp.2
  show ContDiff ℝ ∞ (fun x ↦ (((p x).1 * (p x).2 : ℂˣ) : ℂ))
  simpa using h₁.mul h₂

end Lemmas

end BundleGerbeStable


