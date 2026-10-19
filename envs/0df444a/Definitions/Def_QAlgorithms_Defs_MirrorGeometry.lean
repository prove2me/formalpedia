-- Prove2me | Definitions.Def_QAlgorithms_Defs_MirrorGeometry
-- name    : QAlgorithms_Defs_MirrorGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:12.215207+00:00
-- url     : https://prove2.me/theorems/e554ef67-5449-4f19-a9c0-e5b7d61d5577
-- title:
--   MirrorGeometry
-- statement:
--   MirrorGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MirrorGeometry.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open Filter

namespace QAlgorithms.NoisyOptimization

variable {n m d k b w M K N c out : ℕ}

/-- Open-domain mirror map, 2503.17356 p.31 Definition 4.
The derivative is computed from Phi, and the chosen norm belongs to E.
Strong convexity is deliberately a separate theorem assumption. -/
structure MirrorMap (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  domain : Set E
  feasible : Set E
  domain_open : IsOpen domain
  domain_convex : Convex ℝ domain
  feasible_closure : feasible ⊆ closure domain
  interior_nonempty : (feasible ∩ domain).Nonempty
  Phi : E → ℝ
  strictly_convex : StrictConvexOn ℝ domain Phi
  differentiable : DifferentiableOn ℝ Phi domain
  gradient_onto : ∀ g : E →L[ℝ] ℝ, ∃ x ∈ domain, fderiv ℝ Phi x = g
  gradient_boundary : ∀ z ∈ frontier domain,
    Tendsto (fun x => ‖fderiv ℝ Phi x‖) (nhdsWithin z domain) atTop

/-- Constructed Euclidean nearest point, 2503.17356 pp.29–30.
Completeness and convexity give attainment; no value infimum is used as a point. -/
def euclideanProjection {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (hX : X.Nonempty) (closed : IsClosed X) (convex : Convex ℝ X)
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (exists_norm_eq_iInf_of_complete_convex hX closed.isComplete convex y).choose

/-- Source attained Bregman projection domain, 2503.17356 pp.31–32.
Existence/uniqueness is geometric data, not an optimization success premise. -/
structure MirrorProjectionDomain (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  mirror : MirrorMap E
  attained : ∀ y ∈ mirror.domain, ∃! z,
    z ∈ mirror.feasible ∩ mirror.domain ∧
      ∀ w ∈ mirror.feasible ∩ mirror.domain,
        bregmanDiv mirror.Phi z y ≤ bregmanDiv mirror.Phi w y

/-- Unique attained minimizer on X∩P, 2503.17356 pp.31–32.
Boundary derivative defaults are excluded by the domain subtype. -/
def mirrorProjection {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : MirrorProjectionDomain E) (y : D.mirror.domain) : E :=
  (D.attained y.val y.property).exists.choose

/-- Inverse derivative constructed from the mirror map's onto property,
2503.17356 pp.31–32. Strict convexity supplies mathematical uniqueness;
no unrelated inverse map is an input. -/
def MirrorMap.inverseGradient {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : MirrorMap E) (g : E →L[ℝ] ℝ) : M.domain :=
  ⟨(M.gradient_onto g).choose, (M.gradient_onto g).choose_spec.1⟩

/-- Oracle-independent implementations of attained geometric updates,
2503.17356 pp.29–34. Costs are executed instruction-list lengths and distinct
from function queries; the source imposes no efficiency bound on them. -/
structure GeometryImplementation (d : ℕ) where
  euclideanSet : Set (EuclideanSpace ℝ (Fin d))
  euclidean_nonempty : euclideanSet.Nonempty
  euclidean_closed : IsClosed euclideanSet
  euclidean_convex : Convex ℝ euclideanSet
  mirrorDomain : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d))
  euclideanOps : EuclideanSpace ℝ (Fin d) →
    List (EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  mirrorOps : mirrorDomain.mirror.domain →
    List (EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  euclideanExecution : ∀ y, (euclideanOps y).foldl (fun x op => op x) y =
    euclideanProjection euclideanSet euclidean_nonempty euclidean_closed euclidean_convex y
  mirrorExecution : ∀ y, (mirrorOps y).foldl (fun x op => op x) y.val =
    mirrorProjection mirrorDomain y

/-- Sanity check for the modeled source objects (arxiv-2503.17356v2, PDF pp.29,30,31,32). -/
example {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hX : X.Nonempty)
    (hc : IsClosed X) (hv : Convex ℝ X) (y : EuclideanSpace ℝ (Fin d)) :
    euclideanProjection X hX hc hv y ∈ X :=
  (exists_norm_eq_iInf_of_complete_convex hX hc.isComplete hv y).choose_spec.1

/-- Sanity check for the modeled source objects (arxiv-2503.17356v2, PDF pp.29,30,31,32). -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : MirrorProjectionDomain E) (y : D.mirror.domain) :
    mirrorProjection D y ∈ D.mirror.feasible ∩ D.mirror.domain :=
  (D.attained y.val y.property).exists.choose_spec.1

end QAlgorithms.NoisyOptimization


