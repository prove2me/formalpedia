-- Prove2me | Definitions.Def_InterpolatedFactors
-- name    : InterpolatedFactors
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.301378+00:00
-- url     : https://prove2.me/theorems/332e7c82-bb52-4c6b-96d3-779903e62319
-- statement:
--   This block builds the interpolated free group factors from scratch on ℓ²(G). GroupHilbert(G) is ℓ²(G;ℂ) and GroupOperator(G) its bounded operators. leftTranslations(G) are the operators ξ ↦ ξ(g⁻¹·) for g in G, and groupVonNeumann(G) is the double centralizer of this set, a closed star-subalgebra and C*-algebra. canonicalTrace(T) is the coefficient at the identity of T applied to the delta function at 1. ultraweakOperatorTopology is the infimum of the topologies induced by the maps T ↦ Σₖ ⟨ηₖ, Tξₖ⟩ over square-summable sequences ξ, η of vectors, and groupUltraweakTopology is its restriction to the group von Neumann algebra; FreeGroupRank(n) is the free group on n generators. For a star-projection p in a C*-algebra, the corner is the algebra of x with px = x = xp, a closed C*-algebra with unit p, carrying the induced topology, and normalizedCornerTrace divides a trace τ by a real t. The stabilization of G is the centralizer, in operators on ℓ²(ℕ×G), of the right translations (n,x) ↦ (n,xg), with its own trace Σₖ⟨δ(k,1), Tδ(k,1)⟩, a projection trace in [0,∞] given by Σₖ‖pδ(k,1)‖², and the ultraweak topology; NormalTracialEquiv packages a star-isomorphism that preserves traces and is bicontinuous for given topologies. For the interpolation, selectedProjection(a) is a choice, via Classical.epsilon, of a projection in the stabilization of F₂ whose projection trace equals a, with a default of 0 if none exists, and interpolationScale(r) = 1/√(r−1). A Model is an integer n, a real r, or infinity, with algebra L(F_n), the corner of the F₂ stabilization cut by the selected projection of trace 1/√(r−1) (with the rescaled trace and induced topology), or L(F_∞) for the free group on ℕ. parameterModel sends r in [0,∞] to infinity if r=∞, to the integer model if r is a natural number, and otherwise to the continuous model at r.toReal; InterpolatedFactor, interpolatedTrace and interpolatedTopology give its algebra, trace and topology. No theorem is proved here, and existence of the selected projection is not asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InterpolatedFactors.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InterpolatedFactors.lean; bytes 16..8345
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u uG

open scoped ENNReal

abbrev GroupHilbert (G : Type u) := lp (fun _ : G => ℂ) 2
abbrev GroupOperator (G : Type u) := GroupHilbert G →L[ℂ] GroupHilbert G

def leftTranslations (G : Type u) [Group G] : Set (GroupOperator G) :=
  {T | ∃ g : G, ∀ (ξ : GroupHilbert G) (h : G), (T ξ) h = ξ (g⁻¹ * h)}

def groupVonNeumann (G : Type u) [Group G] : StarSubalgebra ℂ (GroupOperator G) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (leftTranslations G) : Set (GroupOperator G))

def canonicalTrace {G : Type u} [Group G] (T : groupVonNeumann G) : ℂ := by
  classical
  exact ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) 1

@[instance_reducible] def ultraweakOperatorTopology (G : Type u) : TopologicalSpace (GroupOperator G) :=
  ⨅ (ξ : lp (fun _ : ℕ => GroupHilbert G) 2)
    (η : lp (fun _ : ℕ => GroupHilbert G) 2),
    TopologicalSpace.induced
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (T (ξ k)))
      inferInstance

@[instance_reducible] def groupUltraweakTopology (G : Type u) [Group G] :
    TopologicalSpace (groupVonNeumann G) :=
  TopologicalSpace.induced (fun T : groupVonNeumann G => (T : GroupOperator G))
    (ultraweakOperatorTopology G)

abbrev FreeGroupRank (n : ℕ) := FreeGroup (Fin n)

instance groupVN_isClosed (G : Type uG) [Group G] :
    IsClosed (groupVonNeumann G : Set (GroupOperator G)) := by
  unfold groupVonNeumann
  rw [StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

instance groupVN_CStarAlgebra (G : Type uG) [Group G] :
    CStarAlgebra (groupVonNeumann G) := inferInstance

end FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

namespace FreeGroupFactorMain.Amplification

open scoped ENNReal

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def cornerSubalgebra (p : A) (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ A where
  carrier := {x | p*x=x ∧ x*p=x}
  zero_mem' := by simp
  add_mem' hx hy := by constructor <;> simp [mul_add,add_mul,hx.1,hx.2,hy.1,hy.2]
  mul_mem' hx hy := by
    constructor
    · rw [← mul_assoc,hx.1]
    · rw [mul_assoc,hy.2]
  smul_mem' c x hx := by
    constructor
    · rw [mul_smul_comm,hx.1]
    · rw [smul_mul_assoc,hx.2]
  star_mem' hx := by
    constructor
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hx.2
    · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hx.1

abbrev Corner (p : A) (hp : IsStarProjection p) := ↥(cornerSubalgebra p hp)

instance cornerClosed (p : A) (hp : IsStarProjection p) :
    IsClosed (cornerSubalgebra p hp : Set A) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance cornerSemiring (p : A) (hp : IsStarProjection p) : Semiring (Corner p hp) where
  __ : NonUnitalSemiring (Corner p hp) := inferInstance
  one := ⟨p,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  one_mul x := Subtype.ext x.property.1
  mul_one x := Subtype.ext x.property.2

instance cornerRing (p : A) (hp : IsStarProjection p) : Ring (Corner p hp) where
  __ : Semiring (Corner p hp) := inferInstance
  __ : NonUnitalRing (Corner p hp) := inferInstance

instance cornerAlgebra (p : A) (hp : IsStarProjection p) : Algebra ℂ (Corner p hp) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance cornerNormedRing (p : A) (hp : IsStarProjection p) : NormedRing (Corner p hp) where
  __ : Ring (Corner p hp) := inferInstance
  __ : NonUnitalNormedRing (Corner p hp) := inferInstance

instance cornerCStarAlgebra (p : A) (hp : IsStarProjection p) : CStarAlgebra (Corner p hp) where
  __ : NonUnitalCStarAlgebra (Corner p hp) := inferInstance
  __ : NormedRing (Corner p hp) := inferInstance
  __ : Algebra ℂ (Corner p hp) := inferInstance
  norm_smul_le := norm_smul_le

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

@[instance_reducible] def cornerTopology (𝒯 : TopologicalSpace A)
    (p : A) (hp : IsStarProjection p) : TopologicalSpace (Corner p hp) :=
  TopologicalSpace.induced (fun x : Corner p hp => (x : A)) 𝒯

def normalizedCornerTrace (τ : A → ℂ) (t : ℝ) (p : A) (hp : IsStarProjection p)
    (x : Corner p hp) : ℂ := (t : ℂ)⁻¹ * τ x

end

def stabilizedRightTranslations (G : Type u_5) [Group G] : Set (GroupOperator (ℕ × G)) :=
  {T | ∃ g : G, ∀ (ξ : GroupHilbert (ℕ × G)) (x : ℕ × G),
    T ξ x = ξ (x.1,x.2*g)}

def stabilization (G : Type u_6) [Group G] : StarSubalgebra ℂ (GroupOperator (ℕ × G)) :=
  StarSubalgebra.centralizer ℂ (stabilizedRightTranslations G)

instance stabilization_isClosed (G : Type u_7) [Group G] :
    IsClosed (stabilization G : Set (GroupOperator (ℕ × G))) := by
  rw [stabilization,StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

instance stabilization_CStarAlgebra (G : Type u_8) [Group G] : CStarAlgebra (stabilization G) :=
  inferInstance

def stabilizedProjectionTrace {G : Type u_9} [Group G] (p : stabilization G) : ℝ≥0∞ := by
  classical
  exact ∑' k : ℕ, ENNReal.ofReal (‖(p : GroupOperator (ℕ × G))
    (lp.single 2 (k,1) (1 : ℂ))‖ ^ 2)

def stabilizedTrace {G : Type u_10} [Group G] (T : stabilization G) : ℂ := by
  classical
  exact ∑' k : ℕ, inner ℂ (lp.single 2 (k,1) (1 : ℂ))
    ((T : GroupOperator (ℕ × G)) (lp.single 2 (k,1) (1 : ℂ)))

@[instance_reducible] def stabilizationTopology (G : Type u_11) [Group G] :
    TopologicalSpace (stabilization G) :=
  TopologicalSpace.induced (fun T : stabilization G => (T : GroupOperator (ℕ × G)))
    (ultraweakOperatorTopology (ℕ × G))

section
variable {A : Type u_42} {B : Type u_43} [CStarAlgebra A] [CStarAlgebra B]

structure NormalTracialEquiv (τA : A → ℂ) (τB : B → ℂ)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) where
  equiv : A ≃⋆ₐ[ℂ] B
  trace_eq : ∀x,τB (equiv x)=τA x
  normal : @Continuous _ _ 𝒯A 𝒯B equiv
  inverse_normal : @Continuous _ _ 𝒯B 𝒯A equiv.symm

end

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.Interpolation

open Amplification
open scoped ENNReal

abbrev RankTwoProjection := {p : stabilization (FreeGroupRank 2) // IsStarProjection p}

instance rankTwoProjectionInhabited : Inhabited RankTwoProjection :=
  ⟨⟨0,IsStarProjection.zero _⟩⟩

def selectedProjection (a : ℝ) : RankTwoProjection :=
  Classical.epsilon (fun p : RankTwoProjection => stabilizedProjectionTrace p.val=ENNReal.ofReal a)

def interpolationScale (r : ℝ) : ℝ := (Real.sqrt (r-1))⁻¹

inductive Model where
  | integer (n : ℕ)
  | continuous (r : ℝ)
  | infinity

def Model.Algebra : Model → Type
  | .integer n => groupVonNeumann (FreeGroupRank n)
  | .continuous r => Corner (selectedProjection (interpolationScale r)).val
      (selectedProjection (interpolationScale r)).property
  | .infinity => groupVonNeumann (FreeGroup ℕ)

instance modelCStarAlgebra (m : Model) : CStarAlgebra m.Algebra := by
  cases m <;> dsimp only [Model.Algebra] <;> infer_instance

def Model.trace : (m : Model) → m.Algebra → ℂ
  | .integer _ => canonicalTrace
  | .continuous r => normalizedCornerTrace stabilizedTrace (interpolationScale r)
      (selectedProjection (interpolationScale r)).val (selectedProjection (interpolationScale r)).property
  | .infinity => canonicalTrace

@[instance_reducible] def Model.topology : (m : Model) → TopologicalSpace m.Algebra
  | .integer n => groupUltraweakTopology (FreeGroupRank n)
  | .continuous r => cornerTopology (stabilizationTopology (FreeGroupRank 2))
      (selectedProjection (interpolationScale r)).val (selectedProjection (interpolationScale r)).property
  | .infinity => groupUltraweakTopology (FreeGroup ℕ)

def parameterModel (r : ℝ≥0∞) : Model := by
  classical
  exact if r=⊤ then .infinity else
    if h : ∃n : ℕ,r=(n:ℝ≥0∞) then .integer h.choose else .continuous r.toReal

abbrev InterpolatedFactor (r : ℝ≥0∞) := (parameterModel r).Algebra
abbrev interpolatedTrace (r : ℝ≥0∞) := (parameterModel r).trace
abbrev interpolatedTopology (r : ℝ≥0∞) := (parameterModel r).topology



end FreeGroupFactorMain.Interpolation
end
end OAI


