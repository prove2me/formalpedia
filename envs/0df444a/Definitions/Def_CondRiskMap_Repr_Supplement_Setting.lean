-- Prove2me | Definitions.Def_CondRiskMap_Repr_Supplement_Setting
-- name    : CondRiskMap_Repr_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:16:56.43513+00:00
-- url     : https://prove2.me/theorems/9191e6b1-bff5-4f15-9e74-346d345c8681
-- title:
--   §5, pp. 12–14 — compatible stages, multifunction measurability, composite envelopes (5.7), and iterated risk (5.8)
-- statement:
--   Fix a finite filtration $\mathcal F_1\subseteq\cdots\subseteq\mathcal F_T$ on a set $\Omega$. At stage $t$, real locally convex function and measure spaces $\mathcal X_t,\mathcal Y_t$ use the published paired-space setting: functions are pointwise $\mathcal F_t$-measurable, measures are finite signed measures on $(\Omega,\mathcal F_t)$, and every function–measure pair is absolutely integrable. Inclusions of successive function spaces preserve evaluation and give the induced topology. The given inclusion of successive measure spaces preserves restriction to the smaller sigma algebra. Each upper stage's conditioning sigma algebra and lower subspace are exactly the preceding stage. Adjacent risk maps take values in that preceding space; their upper-space endomaps use the published predicates and canonical conjugate domains $\mathcal A_t$.
--
--   Weak* measurability of a multifunction means that, for every $X$, its scalar pairing image hits an open real set on a measurable event. Weak* measurable selections use the published predicate. The composite envelope consists of all measures $\mu\in\mathcal Y_{t+1}$ for which an outer measure and a globally weak* measurable inner selection satisfy
--
--   $$
--   \mu(S)=\int_\Omega\kappa(z)(S)\,d\nu(z),\qquad S\in\mathcal F_{t+1}.
--   $$
--
--   These are actual integrals: their scalar integrands must be integrable against the outer measure's total variation. No membership in $\mathcal Y_{t+1}$ is inferred automatically from a kernel composition. Iterated envelopes use left association of this relation. The iterated risk is the actual backwards composition of the adjacent maps. For Theorem 3 only, $\mathcal F_1$ is trivial and a linear equivalence identifies $\mathcal X_1$ with $\mathbb R$, preserving each constant function's value.
--
--   This interface adds stage compatibility and the missing multifunction and composition objects, while using the immutable definitions of single-stage risk, pairing, conjugate and selection. Indices $0,\ldots,n$ represent source stages $1,\ldots,T$, with $T=n+1$; no theorem targets the unused initial value of envelope recursion. Standing conditions (C) and (C′) and the risk-map hypotheses are separately named predicates, not axioms of a composite envelope.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, pp. 3–4 (paired locally convex spaces, (C), (C′)), p. 8 (Definition 2), pp. 12–14 (§5, (5.7), (5.8), associativity note).

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

namespace CondRiskMap.Repr.Supplement

open MeasureTheory

set_option autoImplicit false

universe u v w

/-- One stage of §5. The immutable paired-space interface is used unchanged.
At an upper stage its `F₁` and `X₁` are identified with the preceding stage by `Inclusion`. -/
structure Stage (Ω : Type u) where
  F : MeasurableSpace Ω
  X : Type v
  Y : Type w
  [addX : AddCommGroup X]
  [moduleX : Module ℝ X]
  [topX : TopologicalSpace X]
  [addY : AddCommGroup Y]
  [moduleY : Module ℝ Y]
  [topY : TopologicalSpace Y]
  [topAddX : IsTopologicalAddGroup X]
  [topSMulX : ContinuousSMul ℝ X]
  [convexX : LocallyConvexSpace ℝ X]
  [topAddY : IsTopologicalAddGroup Y]
  [topSMulY : ContinuousSMul ℝ Y]
  [convexY : LocallyConvexSpace ℝ Y]
  P : @PairedSpaces Ω F X Y addX moduleX topX addY moduleY topY

attribute [instance] Stage.addX Stage.moduleX Stage.topX Stage.addY Stage.moduleY Stage.topY
  Stage.topAddX Stage.topSMulX Stage.convexX Stage.topAddY Stage.topSMulY Stage.convexY


/-- Projection APIs with the stage sigma algebra supplied explicitly. -/
def Stage.eval {Ω : Type u} (H : Stage.{u,v,w} Ω) : H.X →ₗ[ℝ] (Ω → ℝ) :=
  @PairedSpaces.toFun Ω H.F _ _ _ _ _ _ _ _ H.P

def Stage.measure {Ω : Type u} (H : Stage.{u,v,w} Ω) : H.Y →ₗ[ℝ] @SignedMeasure Ω H.F :=
  @PairedSpaces.toMeasure Ω H.F _ _ _ _ _ _ _ _ H.P

def Stage.lower {Ω : Type u} (H : Stage.{u,v,w} Ω) : Submodule ℝ H.X :=
  @PairedSpaces.X₁ Ω H.F _ _ _ _ _ _ _ _ H.P

abbrev Stage.conditioning {Ω : Type u} (H : Stage.{u,v,w} Ω) : MeasurableSpace Ω :=
  @PairedSpaces.F₁ Ω H.F _ _ _ _ _ _ _ _ H.P

/-- Pairing at the stage's own sigma algebra; no extension is used. -/
noncomputable def Stage.pairing {Ω : Type u} (H : Stage.{u,v,w} Ω) (μ : H.Y) (X : H.X) : ℝ :=
  @pair Ω H.F (H.measure μ) (H.eval X)

/-- The signed integral of a specified scalar function on this stage. -/
noncomputable def Stage.integral {Ω : Type u} (H : Stage.{u,v,w} Ω) (μ : H.Y) (f : Ω → ℝ) : ℝ :=
  @pair Ω H.F (H.measure μ) f

variable {Ω : Type u}

/-- Absolute integrability of a scalar function for a stage's actual signed measure. -/
def Stage.ScalarIntegrable (H : Stage.{u,v,w} Ω) (μ : H.Y) (f : Ω → ℝ) : Prop :=
  letI : MeasurableSpace Ω := H.F
  Integrable f (H.measure μ).totalVariation

/-- The inclusion of successive function and measure spaces in §5, p.12.
Measures live on their OWN sigma algebras: `measure_restrict` pins the restriction of
an included measure, rather than silently choosing an extension. -/
structure Inclusion (L H : Stage.{u,v,w} Ω) where
  sigma_le : L.F ≤ H.F
  lower_sigma : H.conditioning = L.F
  incl : L.X →ₗ[ℝ] H.X
  injective : Function.Injective incl
  induced : Topology.IsInducing incl
  eval_incl : ∀ X, H.eval (incl X) = L.eval X
  range_eq : LinearMap.range incl = H.lower
  measureIncl : L.Y →ₗ[ℝ] H.Y
  measure_injective : Function.Injective measureIncl
  measure_restrict : ∀ μ A, MeasurableSet[L.F] A →
    H.measure (measureIncl μ) A = L.measure μ A

/-- A finite compatible family. Indices 0,...,n denote the source's stages 1,...,T,
where T=n+1. A one-stage horizon has no adjacent maps. -/
structure System (Ω : Type u) (n : ℕ) where
  stage : Fin (n+1) → Stage.{u,v,w} Ω
  inclusion : ∀ i : Fin n, Inclusion (stage i.castSucc) (stage i.succ)
  /-- The actual map into the previous space. Its inclusion is the base risk endomap. -/
  risk : ∀ i : Fin n, (stage i.succ).X → (stage i.castSucc).X

/-- The published risk predicates take endomaps of the upper space. -/
def upperRisk {n : ℕ} (D : System.{u,v,w} Ω n) (i : Fin n) :
    (D.stage i.succ).X → (D.stage i.succ).X :=
  fun X => (D.inclusion i).incl (D.risk i X)

/-- The source's canonical envelope (3.8), never an arbitrary representation set. -/
def oneEnvelope {n : ℕ} (D : System.{u,v,w} Ω n) (i : Fin n) :
    Ω → Set (D.stage i.succ).Y :=
  @envelope Ω (D.stage i.succ).F _ _ _ _ _ _ _ _
    (D.stage i.succ).P (upperRisk D i)

/-- Definition 2 for a multifunction, the part missing from the published interface:
scalar images hit each open real set on a measurable event. -/
def WeakStarMultifunction (H : Stage.{u,v,w} Ω) (A : Ω → Set H.Y) : Prop :=
  ∀ X : H.X, ∀ U : Set ℝ, IsOpen U →
    MeasurableSet[H.conditioning] {ω | ∃ μ ∈ A ω, H.pairing μ X ∈ U}

/-- Exactly the published weak* selection predicate. -/
def OneSelection {n : ℕ} (D : System.{u,v,w} Ω n) (i : Fin n)
    (κ : Ω → (D.stage i.succ).Y) : Prop :=
  @IsSelection Ω (D.stage i.succ).F _ _ _ _ _ _ _ _
    (D.stage i.succ).P (upperRisk D i) κ

/-- (5.7), with ambient membership and a meaningful integral on EVERY measurable set.
The measure at the left is already in the target paired measure space. -/
def Composite {L H : Stage.{u,v,w} Ω} (A : Ω → Set L.Y) (B : Ω → Set H.Y)
    (ω : Ω) : Set H.Y :=
  {μ | ∃ ν ∈ A ω, ∃ κ : Ω → H.Y,
    (∀ z, κ z ∈ B z) ∧
    (@IsWeakStarMeasurable Ω H.F _ _ _ _ _ _ _ _ H.P κ) ∧
    ∀ S : Set Ω, MeasurableSet[H.F] S →
      L.ScalarIntegrable ν (fun z => H.measure (κ z) S) ∧
      H.measure μ S = L.integral ν (fun z => H.measure (κ z) S)}

/-- (5.8) as actual backwards composition, with no auxiliary probability measure. -/
def riskToFirst {n : ℕ} (D : System.{u,v,w} Ω n) :
    (i : Fin (n+1)) → (D.stage i).X → (D.stage 0).X :=
  Fin.induction (fun X => X) (fun i prev X => prev (D.risk i X))

/-- Left-associated (5.7). The first stage is an unused probability set,
so that the next clause starts with A₁ rather than introducing a fictitious stage-0 kernel.
The zero-stage value is used only for well-typed recursion and is not a theorem target. -/
def iteratedEnvelope {n : ℕ} (D : System.{u,v,w} Ω n) :
    (i : Fin (n+1)) → Ω → Set (D.stage i).Y :=
  Fin.induction (fun _ => @Prob Ω (D.stage 0).F _ _ _ _ _ _ _ _ (D.stage 0).P)
    (fun i prev => if i.val = 0 then oneEnvelope D i
      else Composite prev (oneEnvelope D i))

/-- Standing (C), (C′) at every adjacent pair. These are not (K) or HasIndicators. -/
def Standing {n : ℕ} (D : System.{u,v,w} Ω n) : Prop :=
  ∀ i : Fin n,
    @CondC Ω (D.stage i.succ).F _ _ _ _ _ _ _ _ (D.stage i.succ).P ∧
    @CondC' Ω (D.stage i.succ).F _ _ _ _ _ _ _ _ (D.stage i.succ).P

/-- The source hypotheses on the adjacent risk maps. -/
def RiskHypotheses {n : ℕ} (D : System.{u,v,w} Ω n) : Prop :=
  ∀ i : Fin n,
    @IsCondRiskMapping Ω (D.stage i.succ).F _ _ _ _ _ _ _ _
      (D.stage i.succ).P (upperRisk D i) ∧
    PosHomogeneous (upperRisk D i) ∧
    @IsLsc Ω (D.stage i.succ).F _ _ _ _ _ _ _ _
      (D.stage i.succ).P (upperRisk D i)

/-- The scalar identification X₁=ℝ on p.13, stated without selecting a sample point.
The equation asserts that the specified linear equivalence is the function's constant value. -/
structure TrivialFirst {n : ℕ} (D : System.{u,v,w} Ω n) where
  sigma : (D.stage 0).F = ⊥
  value : (D.stage 0).X ≃ₗ[ℝ] ℝ
  eval_value : ∀ X ω, (D.stage 0).eval X ω = value X

end CondRiskMap.Repr.Supplement


