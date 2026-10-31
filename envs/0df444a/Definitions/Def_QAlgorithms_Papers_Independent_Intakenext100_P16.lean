-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P16
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P16
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:09:26.882983+00:00
-- url     : https://prove2.me/theorems/edcb3b7c-032a-445f-a6d7-4454a32ad497
-- title:
--   Definitions for Differentiable Cohomology of Gauge Groups
-- statement:
--   The objects the formalized statements of *Differentiable Cohomology of Gauge Groups* (arXiv:math/0011069) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FrechetAbelianLieData`: PDF p. 3: an abelian coefficient Lie group in the paper's Fréchet convention. The supplied model carries its complete, metrizable, compatible additive uniformity; the actual manifold atlas and its topology are retained. The global exponential is parametrized by tangent vectors using the chart at zero. Its derivative is the identity in this tangent identification. The accepted directional calculus is used without a normability assumption.
--   - `measurablePrelocal`: PDF p. 11: actual Borel-measurable A-valued functions on open subsets. Measurability here is pointwise, with no almost-everywhere quotient. Restriction is induced by the actual inclusion of open subspaces.
--   - `measurableFunctionSheaf`: PDF p. 11: the sheaf of germs of measurable functions, constructed by sheafifying the measurable local predicate. A section is an actual function locally agreeing with measurable functions. This retains gluing over arbitrary open covers without imposing countability on those covers.
--   - `constantMeasurableSection`: Constant functions give sections of the measurable coefficient sheaf.
-- source:
--   Differentiable Cohomology of Gauge Groups, arXiv:math/0011069v1, https://arxiv.org/abs/math/0011069v1

import Mathlib
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Flasque
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29

/-!
Jean-Luc Brylinski, Differentiable Cohomology of Gauge Groups,
arXiv:math/0011069v1. The surviving statement is Lemma 2.5 (PDF p. 11).
The other inventoried nodes are explicitly deferred in the assigned HARD.md.
New definitions use the given topologies and atlases. No norm is imposed on
Fréchet coefficient models. Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P16

open CategoryTheory TopologicalSpace Opposite Filter Topology

universe u v w

/-- PDF p. 3: an abelian coefficient Lie group in the paper's Fréchet
convention. The supplied model carries its complete, metrizable, compatible
additive uniformity; the actual manifold atlas and its topology are retained.
The global exponential is parametrized by tangent vectors using the chart at
zero. Its derivative is the identity in this tangent identification.
The accepted directional calculus is used without a normability assumption. -/
structure FrechetAbelianLieData
    (E : Type v) (A : Type w)
    [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    [AddCommGroup A] [TopologicalSpace A] [ChartedSpace E A] where
  uniform_add : IsUniformAddGroup E
  complete : CompleteSpace E
  metrizable : MetrizableSpace E
  lie : QAlgorithms.Papers.Independent.Renew46.P29.DirectionalAddLieGroup ℝ E A
  paracompact : ParacompactSpace A
  exp : E → A
  exp_smooth : QAlgorithms.Papers.Independent.Renew46.P29.ManifoldSmoothOn ℝ
    (E := E) (F := E) Set.univ exp
  exp_zero : exp 0 = 0
  exp_line : ∀ (x : E) (s t : ℝ),
    exp ((s + t) • x) = exp (s • x) + exp (t • x)
  exp_tangent : ∀ x : E,
    Tendsto (fun t : ℝ => t⁻¹ •
      (chartAt E (0 : A) (exp (t • x)) - chartAt E (0 : A) (0 : A)))
      (𝓝[≠] (0 : ℝ)) (𝓝 x)

/-- Sanity at time zero: every exponential curve starts at the identity. -/
example {E : Type v} {A : Type w}
    [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    [AddCommGroup A] [TopologicalSpace A] [ChartedSpace E A]
    (D : FrechetAbelianLieData E A) (x : E) : D.exp ((0 : ℝ) • x) = 0 := by
  simpa only [zero_smul] using D.exp_zero

/-- PDF p. 11: actual Borel-measurable A-valued functions on open subsets.
Measurability here is pointwise, with no almost-everywhere quotient.
Restriction is induced by the actual inclusion of open subspaces. -/
def measurablePrelocal (X : TopCat.{u}) (A : Type w) [TopologicalSpace A] :
    TopCat.PrelocalPredicate (fun _ : X => A) where
  pred {U} f := @Measurable U A (borel U) (borel A) f
  res {_ _} i f hf :=
    hf.comp (Opens.isOpenEmbedding_of_le i.le).continuous.borel_measurable

/-- PDF p. 11: the sheaf of germs of measurable functions, constructed
by sheafifying the measurable local predicate. A section is an actual
function locally agreeing with measurable functions. This retains gluing
over arbitrary open covers without imposing countability on those covers. -/
def measurableFunctionSheaf (X : TopCat.{u}) (A : Type w) [TopologicalSpace A] :
    TopCat.Sheaf (Type (max u w)) X :=
  TopCat.subsheafToTypes (measurablePrelocal X A).sheafify

/-- Constant functions give sections of the measurable coefficient sheaf. -/
def constantMeasurableSection (X : TopCat.{u}) (A : Type w) [TopologicalSpace A]
    (U : Opens X) (a : A) : (measurableFunctionSheaf X A).obj.obj (op U) :=
  ⟨fun _ => a, TopCat.PrelocalPredicate.sheafifyOf
    (continuous_const.borel_measurable)⟩

/-- Sanity: a constant section retains its actual value at every point. -/
example (X : TopCat.{u}) (A : Type w) [TopologicalSpace A]
    (U : Opens X) (a : A) (x : U) :
    (constantMeasurableSection X A U a).val x = a := rfl

/-- Sanity: restriction of constant sections is the same constant section. -/
example (X : TopCat.{u}) (A : Type w) [TopologicalSpace A]
    {U V : Opens X} (i : V ⟶ U) (a : A) :
    (measurableFunctionSheaf X A).obj.map i.op (constantMeasurableSection X A U a) =
      constantMeasurableSection X A V a := by
  apply Subtype.ext
  rfl

/-- Sanity: simplicial degree zero has one tuple and the section value is A,
rather than the zero group or an almost-everywhere equivalence class. -/
example (G : Type u) (A : Type w) [TopologicalSpace G] [TopologicalSpace A]
    (a : A) :
    (constantMeasurableSection (TopCat.of (Fin 0 → G)) A ⊤ a).val
      ⟨fun i => Fin.elim0 i, by trivial⟩ = a := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P16


