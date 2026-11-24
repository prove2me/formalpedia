-- Prove2me | Definitions.Def_EkelandVP_Constraints_Supplement_sobolevPaths
-- name    : EkelandVP_Constraints_Supplement_sobolevPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:23:31.26053+00:00
-- url     : https://prove2.me/theorems/ca125fad-70d4-40c9-b113-8d34f0f97a1a
-- title:
--   H¹ paths, topology (6.1), canonical smooth coordinate families and split submanifolds
-- statement:
--   Let $M$ be a smooth manifold modeled on a real Hilbert space $H$. An **H¹ path** has a continuous representative $c:[0,1]\to M$ and a finite strict partition $0=a_0<\cdots<a_n=1$, with a smooth chart $\phi_i$ on each piece. Its coordinate representative is absolutely continuous and has square-integrable velocity: for some $v_i\in L^2([a_{i-1},a_i];H)$,
--   $$
--   \phi_i(c(t))=\phi_i(c(a_{i-1}))+\int_{a_{i-1}}^t v_i(s)\,ds.
--   $$
--   The topology in (6.1) controls the uniform coordinate error and the sum of the $L^2$ coordinate velocity errors. The endpoint set is
--   $$
--   V_{p,q}=\{c\in H^1([0,1];M):c(0)=p,\ c(1)=q\}.
--   $$
--   Smooth paths are smooth on the closed interval, using within derivatives at the endpoints. The endpoint set contains every H¹ curve with those endpoints, including nonsmooth curves and the case $p=q$.
--
--   For the canonical smooth structure, an open-parameter family is smooth locally when, on a common adapted partition, the initial coordinate values and the $L^2$ velocities vary smoothly in their normed spaces. A split smooth submanifold is locally flattened by homeomorphic smooth charts to closed complemented linear subspaces of the H¹ model $H\times L^2([0,1];H)$. Forward chart smoothness is tested on all such smooth families; inverse chart smoothness is required directly. These definitions do not assume endpoint density or the submanifold theorem.
--
--   **Formalization Note** Continuous paths are actual maps on the closed interval. Their constant extensions are used only for derivatives within that interval. Integral reconstruction specifies the absolutely continuous representative and excludes singular continuous paths with a.e. zero pointwise derivative. Coordinate tubes use a strict positive radius and an existential uniform error bound, avoiding a real supremum's default on unbounded sets. Generating the topology with these open tubes gives the same neighborhoods as (6.1). Closed, continuously complemented subspaces express the split Hilbert submanifold convention. The product sup norm is equivalent to its Hilbert norm. No path-space Riemannian metric or theorem about it is postulated.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), pp. 341–344, §6, (6.1), the smooth structure following (6.12), and Lemma 6.2 (PDF 18–21); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
set_option autoImplicit false

open Set MeasureTheory Manifold
open scoped ContDiff

namespace EkelandVP.Constraints.Supplement

universe u

/-- The closed time interval; paths have actual continuous representatives. -/
abbrev Time := Set.Icc (0 : ℝ) 1

/-- Constant extension outside the time interval, used only for within derivatives. -/
noncomputable def extendPath {M : Type u} [TopologicalSpace M] (c : C(Time, M)) (t : ℝ) : M :=
  c (projIcc 0 1 zero_le_one t)

/-- Coordinate H¹ regularity, with the absolutely continuous representative.
The integral reconstruction excludes singular continuous curves with a.e. zero derivative. -/
def H1On {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℝ → H) (a b : ℝ) : Prop :=
  ∃ v : ℝ → H, MemLp v 2 (volume.restrict (Icc a b)) ∧
    ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s

/-- A finite strict partition and one smooth chart per subinterval. -/
structure PathPartition (H M : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M] where
  n : ℕ
  a : Fin (n + 1) → ℝ
  increasing : StrictMono a
  first : a 0 = 0
  last : a (Fin.last n) = 1
  chart : Fin n → OpenPartialHomeomorph M H
  smooth : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℝ, H) ∞ M

variable {H M : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- The path stays in the chosen chart on each closed subinterval. -/
def PathPartition.Adapted (P : PathPartition H M) (c : C(Time, M)) : Prop :=
  ∀ i t, t ∈ Icc (P.a i.castSucc) (P.a i.succ) →
    extendPath c t ∈ (P.chart i).source

/-- The full coordinate H¹ path space, with no smoothness restriction on its curves. -/
def IsSobolevPath (c : C(Time, M)) : Prop :=
  ∃ P : PathPartition H M, P.Adapted c ∧ ∀ i,
    H1On (fun t => P.chart i (extendPath c t)) (P.a i.castSucc) (P.a i.succ)

abbrev SobolevPaths (H M : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M] :=
  {c : C(Time, M) // IsSobolevPath (H := H) c}

/-- Coordinate velocity on a chart subinterval. -/
noncomputable def chartVelocity (P : PathPartition H M) (c : C(Time, M)) (i : Fin P.n) : ℝ → H :=
  derivWithin (fun t => P.chart i (extendPath c t)) (Icc (P.a i.castSucc) (P.a i.succ))

/-- An open-radius version of the coordinate neighborhoods (6.1).
The existential uniform bound avoids an unbounded real supremum's default value. -/
def pathTube (P : PathPartition H M) (c : SobolevPaths H M) (ε : ℝ) : Set (SobolevPaths H M) :=
  {d | P.Adapted d.val ∧ ∃ r : ℝ, 0 ≤ r ∧
    (∀ i t, t ∈ Icc (P.a i.castSucc) (P.a i.succ) →
      ‖P.chart i (extendPath c.val t) - P.chart i (extendPath d.val t)‖ ≤ r) ∧
    r + ∑ i : Fin P.n, Real.sqrt (∫ t in (P.a i.castSucc)..(P.a i.succ),
      ‖chartVelocity P c.val i t - chartVelocity P d.val i t‖ ^ 2) < ε}

/-- Topology (6.1), generated by all adapted coordinate tubes. -/
noncomputable instance sobolevPathTopology : TopologicalSpace (SobolevPaths H M) :=
  TopologicalSpace.generateFrom {U | ∃ (P : PathPartition H M) (c : SobolevPaths H M)
    (ε : ℝ), P.Adapted c.val ∧ 0 < ε ∧ U = pathTube P c ε}

/-- Smoothness of a path includes one-sided smoothness at both endpoints. -/
def SmoothPath (c : SobolevPaths H M) : Prop :=
  ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, H) ∞ (extendPath c.val) (Icc 0 1)

/-- All H¹ curves with the prescribed endpoints, including the case p = q. -/
def fixedEndpoints (p q : M) : Set (SobolevPaths H M) :=
  {c | extendPath c.val 0 = p ∧ extendPath c.val 1 = q}

variable [CompleteSpace H]

/-- H¹ coordinate data: initial value and L² derivative on every chart subinterval. -/
abbrev PartitionModel (P : PathPartition H M) :=
  (i : Fin P.n) → H × Lp H 2 (volume.restrict (Icc (P.a i.castSucc) (P.a i.succ)))

/-- The canonical smooth structure described through coordinate plots. A family is smooth
locally exactly when its initial coordinate values and L² coordinate velocities vary smoothly.
No density, endpoint transversality, or variational existence is assumed here. -/
def SmoothH1Family {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : B → SobolevPaths H M) (U : Set B) : Prop :=
  ContinuousOn f U ∧ ∀ b ∈ U, ∃ (W : Set B) (P : PathPartition H M),
    IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ (∀ z ∈ W, P.Adapted (f z).val) ∧
    ∃ v : B → PartitionModel P, ContDiffOn ℝ ∞ v W ∧
      ∀ z ∈ W, ∀ i : Fin P.n,
        (v z i).1 = P.chart i (extendPath (f z).val (P.a i.castSucc)) ∧
        (∀ᵐ t ∂(volume.restrict (Icc (P.a i.castSucc) (P.a i.succ))),
          (v z i).2 t = chartVelocity P (f z).val i t)

/-- The Banach model of H¹ fields, isomorphic to H × L²([0,1];H).
The product sup norm is equivalent to its Hilbert norm. -/
abbrev H1Model (H : Type u) [NormedAddCommGroup H] :=
  H × Lp H 2 (volume.restrict (Icc (0 : ℝ) 1))

/-- Forward smoothness of a path chart tested on all canonical smooth H¹ plots. -/
def H1ChartSmooth (e : OpenPartialHomeomorph (SobolevPaths H M) (H1Model H)) : Prop :=
  SmoothH1Family e.symm e.target ∧
    ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
      (U : Set B) (f : B → SobolevPaths H M),
      IsOpen U → SmoothH1Family f U → MapsTo f U e.source →
        ContDiffOn ℝ ∞ (e ∘ f) U

/-- A split smooth embedded submanifold: canonical smooth local charts flatten the set to
closed, continuously complemented linear subspaces of the H¹ model. This is a definition
of the geometric conclusion, not a structure postulating the endpoint theorem. -/
def IsSplitH1Submanifold (S : Set (SobolevPaths H M)) : Prop :=
  ∀ c ∈ S, ∃ (e : OpenPartialHomeomorph (SobolevPaths H M) (H1Model H))
    (K : Submodule ℝ (H1Model H)), c ∈ e.source ∧ H1ChartSmooth e ∧
      IsClosed (K : Set (H1Model H)) ∧
      (∃ P : H1Model H →L[ℝ] H1Model H,
        (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x) ∧
      ∀ d ∈ e.source, d ∈ S ↔ e d ∈ K

end EkelandVP.Constraints.Supplement


