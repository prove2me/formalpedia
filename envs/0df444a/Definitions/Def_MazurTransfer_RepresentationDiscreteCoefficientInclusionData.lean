-- Prove2me | Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientInclusionData
-- name    : MazurTransfer_RepresentationDiscreteCoefficientInclusionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:08:06.650503+00:00
-- url     : https://prove2.me/theorems/f41cca38-fa68-4807-a18c-cdaebc460e40
-- title:
--   Original representation coefficient inclusions and induced continuous H1 maps
-- statement:
--   Retain the original homomorphism from the discrete coefficient group of a representation through an intertwiner into an existing multiplicative coefficient action, its injectivity and equivariance laws, the kernel/image computation from a given exact representation sequence, and its induced continuous H1 map. Every complete original context is retained. All five original types and both nonproof constructor values are compared. Named downstream consumer: the actual norm-character continuous H1 exact sequence. The packaged computation and specialization facts receive no extra owned theorem acceptance.
-- source:
--   Original MazurTheorem RepresentationDiscreteCoefficientInclusion, Apache-2.0. All original declaration bodies are retained; only imports are replaced by checked public dependencies.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an injective representation intertwiner maps its discrete
coefficient group into an existing multiplicative coefficient action.
Named downstream consumer: exactness at continuous H1 of actual norm kernels.
-/
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData

noncomputable section
namespace MazurTransfer.RepresentationDiscreteCoefficientInclusion
open RepresentationDiscreteCoefficients
variable {k G V W M : Type} [Semiring k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [CommGroup M] [MulDistribMulAction G M] [Module k (Additive M)]
variable (σ : Representation k G V) (ρ : Representation k G (Additive M))
  (τ : Representation k G W)
variable (i : Representation.IntertwiningMap σ ρ) (p : Representation.IntertwiningMap ρ τ)

def toIntertwining : Coefficient σ →* M where
  toFun x := (i x.val).toMul
  map_one' := congrArg Additive.toMul (map_zero i)
  map_mul' x y := congrArg Additive.toMul (map_add i x.val y.val)

theorem toIntertwining_injective (hi : Function.Injective i) :
    Function.Injective (toIntertwining σ ρ i) := by
  intro x y h
  apply Coefficient.ext
  apply hi
  exact congrArg Additive.ofMul h

theorem toIntertwining_equivariant
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (g : G) (x : Coefficient σ) :
    toIntertwining σ ρ i (g • x) = g • toIntertwining σ ρ i x := by
  apply Additive.ofMul.injective
  change i (σ g x.val) = Additive.ofMul (g • (i x.val).toMul)
  rw [← hρ]
  exact Representation.IntertwiningMap.isIntertwining σ ρ i g x.val

theorem coefficient_exact
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) (m : M) :
    fromIntertwining ρ τ p m = 1 ↔ ∃ x : Coefficient σ, toIntertwining σ ρ i x = m := by
  constructor
  · intro hm
    have hm' : p (Additive.ofMul m) = 0 := congrArg Coefficient.val hm
    have hr : Additive.ofMul m ∈ LinearMap.range i.toLinearMap := by
      rw [hk]
      exact hm'
    obtain ⟨v, hv⟩ := hr
    exact ⟨⟨v⟩, congrArg Additive.toMul hv⟩
  · rintro ⟨x, hx⟩
    apply Coefficient.ext
    have hr : Additive.ofMul m ∈ LinearMap.range i.toLinearMap :=
      ⟨x.val, congrArg Additive.ofMul hx⟩
    rw [hk] at hr
    exact hr

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]

def inclusionH1
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m)) :
    ContinuousFirstCohomologyPresentation.H1 G (Coefficient σ) →+
      ContinuousFirstCohomologyPresentation.H1 G M :=
  ContinuousFirstCohomologyCoefficientMap.coefficientMap G (Coefficient σ) M
    (toIntertwining σ ρ i) (toIntertwining_equivariant σ ρ i hρ) continuous_of_discreteTopology

end MazurTransfer.RepresentationDiscreteCoefficientInclusion
#print axioms MazurTransfer.RepresentationDiscreteCoefficientInclusion.coefficient_exact
#print axioms MazurTransfer.RepresentationDiscreteCoefficientInclusion.inclusionH1


