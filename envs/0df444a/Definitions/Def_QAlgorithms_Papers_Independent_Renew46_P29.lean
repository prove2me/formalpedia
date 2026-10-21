-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29
-- name    : QAlgorithms_Papers_Independent_Renew46_P29
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:55:47.273774+00:00
-- url     : https://prove2.me/theorems/f85eb272-dc8c-4f74-833c-d168a98eaf83
-- title:
--   Definitions for Abelian extensions of infinite-dimensional Lie groups
-- statement:
--   The objects the formalized statements of *Abelian extensions of infinite-dimensional Lie groups* (arXiv:math/0402303) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NormalizedTwoCocycle`: PDF p. 7, Lemma II.1: normalized inhomogeneous group two-cocycles. The printed second argument gg' in the second summand is corrected to g''; associativity and Appendix B fix this reading.
--   - `extensionMul`: PDF p. 7, equation (2.1): the actual twisted product on A × G.
--   - `extensionInv`: PDF p. 7, equation (2.2): the inverse in the twisted product.
--   - `ScalarSmoothOn`: PDF p. 5: scalar smoothness over R or C, reusing the accepted real smoothness predicate. Real scalars on the models are restricted along the canonical inclusion. The additional scalar-linear first differential retains the complex calculus: real smoothness alone would admit complex conjugation. On open locally convex domains, real smoothness with a K-linear differential is equivalent to smoothness in the paper's K-directional calculus.
--   - `LocallyConvexModel`: PDF p. 5: Hausdorff locally convex topological vector models. For complex models local convexity refers to the compatible underlying real vector space.
--   - `ScalarAtlas`: PDF p. 5: the accepted real atlas compatibility, together with the scalar-linear transition differentials required over C. This extends the imported atlas predicate without declaring another DirectionalAtlas.
--   - `ManifoldSmoothOn`: PDF p. 5: smoothness on an open part of a manifold, using its source and target atlases. The source domain and both chart domains enter the coordinate condition. This extends pinned Next46.P35.DirectionalManifoldSmooth to open subsets and to real or complex scalars.
--   - `DirectionalLieGroup`: PDF p. 5: the given Hausdorff manifold and group operations form a Lie group. The supplied topology and atlas, rather than an unrelated structure, are used.
--   - `DirectionalAddLieGroup`: PDF p. 5: an abelian Lie group, with additive notation.
--   - `homogeneousTransform`: PDF p. 61, Definition B.2: the homogeneous transform Phi.
--   - `deletionDifferential`: PDF p. 61: Alexander--Spanier's alternating deletion differential.
--   - `cumulativeTuple`: PDF p. 61: cumulative products (1,g0,g0g1,...), in order even for a noncommutative group. The empty prefix is the identity.
--   - `groupDifferential`: PDF p. 61, Definition B.2: dG = Phi inverse composed with dAS composed with Phi. The definition does not assume the formula in Lemma B.3.
--   - `mergeAdjacent`: PDF p. 61: replacing two adjacent entries by their product.
--   - `inhomogeneousDifferential`: PDF pp. 61--62, Lemma B.3: the explicit inhomogeneous formula, including n=0. The middle sum is empty in degree zero.
--   - `LocallySmoothCochain`: PDF p. 61, Definition B.2: normalized cochains smooth on an open identity neighborhood. In degree zero the normalization has no indices, as required.
--   - `cupProduct`: PDF p. 78: the ordered, action-twisted cup product. The initial block's product acts on the second cochain, also when either degree is zero.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, https://arxiv.org/abs/math/0402303v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

/-!
Statements from K.-H. Neeb, Abelian extensions of infinite-dimensional Lie groups,
arXiv:math/0402303v1. New definitions are confined to this paper.
The pinned accepted Next46.P35 supplies real directional calculus and atlas
compatibility. Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

section AlgebraicExtension

variable {G : Type u} [Group G] {A : Type v} [AddCommGroup A]
variable [DistribMulAction G A]

/-- PDF p. 7, Lemma II.1: normalized inhomogeneous group two-cocycles.
The printed second argument gg' in the second summand is corrected to g'';
associativity and Appendix B fix this reading. -/
def NormalizedTwoCocycle (f : G → G → A) : Prop :=
  (∀ g, f g 1 = 0) ∧ (∀ g, f 1 g = 0) ∧
    ∀ g h k, f g h + f (g * h) k = g • f h k + f g (h * k)

/-- PDF p. 7, equation (2.1): the actual twisted product on A × G. -/
def extensionMul (f : G → G → A) (x y : A × G) : A × G :=
  (x.1 + x.2 • y.1 + f x.2 y.2, x.2 * y.2)

/-- PDF p. 7, equation (2.2): the inverse in the twisted product. -/
def extensionInv (f : G → G → A) (x : A × G) : A × G :=
  (-(x.2⁻¹ • (x.1 + f x.2 x.2⁻¹)), x.2⁻¹)

/-- Sanity: the zero cocycle satisfies both normalizations and associativity. -/
example : NormalizedTwoCocycle (fun _ _ : G => (0 : A)) := by
  simp [NormalizedTwoCocycle]

/-- Sanity: the zero cocycle gives the semidirect-product multiplication. -/
example (x y : A × G) :
    extensionMul (fun _ _ => (0 : A)) x y =
      (x.1 + x.2 • y.1, x.2 * y.2) := by
  simp [extensionMul]

end AlgebraicExtension

/-- Product charts on the ordinary vector-space product; the Mathlib
constructor supplies exactly the source and target product atlas. -/
local instance productManifoldCharts
    (E F M N : Type*) [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N] : ChartedSpace (E × F) (M × N) :=
  prodChartedSpace E M F N

/-- Finite product charts on the ordinary function-space model, including
n=0. This is the Mathlib finite-product atlas, with no tagged algebra needed. -/
local instance cochainManifoldCharts
    (n : ℕ) (E G : Type*) [TopologicalSpace E] [TopologicalSpace G]
    [ChartedSpace E G] : ChartedSpace (Fin n → E) (Fin n → G) :=
  piChartedSpace (fun _ : Fin n => E) (fun _ : Fin n => G)

section DirectionalCalculus

variable (K : Type*) [RCLike K]
variable {E F : Type*}
variable [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- PDF p. 5: scalar smoothness over R or C, reusing the accepted real
smoothness predicate. Real scalars on the models are restricted along the
canonical inclusion. The additional scalar-linear first differential retains
the complex calculus: real smoothness alone would admit complex conjugation.
On open locally convex domains, real smoothness with a K-linear differential
is equivalent to smoothness in the paper's K-directional calculus. -/
def ScalarSmoothOn (U : Set E) (f : E → F) : Prop :=
  letI : Module ℝ E := Module.compHom E (algebraMap ℝ K)
  letI : Module ℝ F := Module.compHom F (algebraMap ℝ K)
  QAlgorithms.Papers.Independent.Next46.P35.DirectionalSmoothOn U f ∧
    ∃ d : E → E →ₗ[K] F, ∀ x ∈ U, ∀ h : E,
      Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • h) - f x))
        (𝓝[≠] (0 : ℝ)) (𝓝 (d x h))

/-- Sanity: zero is smooth over both scalar fields, with zero differential. -/
example (U : Set E) : ScalarSmoothOn K U (fun _ : E => (0 : F)) := by
  dsimp [ScalarSmoothOn]
  constructor
  · refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      rfl
    · intro n
      exact continuousOn_const
    · intro n x hx a h
      simpa only [sub_self, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))
  · refine ⟨fun _ => 0, ?_⟩
    intro x hx h
    simpa only [sub_self, smul_zero, LinearMap.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

/-- PDF p. 5: Hausdorff locally convex topological vector models. For complex
models local convexity refers to the compatible underlying real vector space. -/
def LocallyConvexModel (E : Type*) [AddCommGroup E] [Module K E]
    [TopologicalSpace E] : Prop :=
  IsTopologicalAddGroup E ∧ ContinuousSMul K E ∧ T2Space E ∧
    ∃ realModule : Module ℝ E,
      letI := realModule
      IsScalarTower ℝ K E ∧ LocallyConvexSpace ℝ E

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
variable [ChartedSpace E M] [ChartedSpace F N]

/-- PDF p. 5: the accepted real atlas compatibility, together with the
scalar-linear transition differentials required over C. This extends the
imported atlas predicate without declaring another DirectionalAtlas. -/
def ScalarAtlas : Prop :=
  (letI : Module ℝ E := Module.compHom E (algebraMap ℝ K)
   QAlgorithms.Papers.Independent.Next46.P35.DirectionalAtlas (E := E) (M := M)) ∧
    ∀ c ∈ atlas E M, ∀ e ∈ atlas E M,
      ScalarSmoothOn K (c.symm.trans e).source (c.symm.trans e)

/-- PDF p. 5: smoothness on an open part of a manifold, using its source and
target atlases. The source domain and both chart domains enter the coordinate
condition. This extends pinned Next46.P35.DirectionalManifoldSmooth to open
subsets and to real or complex scalars. -/
def ManifoldSmoothOn (U : Set M) (f : M → N) : Prop :=
  ContinuousOn f U ∧
    ∀ c ∈ atlas E M, ∀ e ∈ atlas F N,
      ScalarSmoothOn K
        (c.target ∩ (fun x => c.symm x) ⁻¹' U ∩
          (fun x => f (c.symm x)) ⁻¹' e.source)
        (fun x => e (f (c.symm x)))

/-- PDF p. 5: the given Hausdorff manifold and group operations form a Lie
group. The supplied topology and atlas, rather than an unrelated structure,
are used. -/
def DirectionalLieGroup (E G : Type*) [AddCommGroup E] [Module K E]
    [TopologicalSpace E] [Group G] [TopologicalSpace G] [ChartedSpace E G] : Prop :=
  LocallyConvexModel K E ∧ T2Space G ∧ ScalarAtlas K (E := E) (M := G) ∧
    ManifoldSmoothOn K (E := (E × E)) (F := E) Set.univ
      (fun p : G × G => p.1 * p.2) ∧
    ManifoldSmoothOn K (E := E) (F := E) Set.univ (fun g : G => g⁻¹)

/-- PDF p. 5: an abelian Lie group, with additive notation. -/
def DirectionalAddLieGroup (F A : Type*) [AddCommGroup F] [Module K F]
    [TopologicalSpace F] [AddCommGroup A] [TopologicalSpace A] [ChartedSpace F A] : Prop :=
  LocallyConvexModel K F ∧ T2Space A ∧ ScalarAtlas K (E := F) (M := A) ∧
    ManifoldSmoothOn K (E := (F × F)) (F := F) Set.univ
      (fun p : A × A => p.1 + p.2) ∧
    ManifoldSmoothOn K (E := F) (F := F) Set.univ (fun a : A => -a)

end DirectionalCalculus

section GroupCochains

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]
variable [DistribMulAction G A]

/-- PDF p. 61, Definition B.2: the homogeneous transform Phi. -/
def homogeneousTransform (n : ℕ) (f : (Fin n → G) → A)
    (g : Fin (n + 1) → G) : A :=
  g 0 • f (fun i => (g i.castSucc)⁻¹ * g i.succ)

/-- PDF p. 61: Alexander--Spanier's alternating deletion differential. -/
def deletionDifferential (n : ℕ) (F : (Fin (n + 1) → G) → A)
    (g : Fin (n + 2) → G) : A :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F (fun j => g (i.succAbove j))

/-- PDF p. 61: cumulative products (1,g0,g0g1,...), in order even for a
noncommutative group. The empty prefix is the identity. -/
def cumulativeTuple {n : ℕ} (g : Fin n → G) (i : Fin (n + 1)) : G :=
  ((List.ofFn g).take i.val).prod

/-- PDF p. 61, Definition B.2: dG = Phi inverse composed with dAS composed
with Phi. The definition does not assume the formula in Lemma B.3. -/
def groupDifferential (n : ℕ) (f : (Fin n → G) → A)
    (g : Fin (n + 1) → G) : A :=
  deletionDifferential n (homogeneousTransform n f) (cumulativeTuple g)

/-- PDF p. 61: replacing two adjacent entries by their product. -/
def mergeAdjacent {n : ℕ} (g : Fin (n + 1) → G) (j : Fin n) : Fin n → G :=
  fun k => if k < j then g k.castSucc
    else if k = j then g k.castSucc * g k.succ else g k.succ

/-- PDF pp. 61--62, Lemma B.3: the explicit inhomogeneous formula, including
n=0. The middle sum is empty in degree zero. -/
def inhomogeneousDifferential (n : ℕ) (f : (Fin n → G) → A)
    (g : Fin (n + 1) → G) : A :=
  g 0 • f (fun i => g i.succ) +
    (∑ j : Fin n, (-1 : ℤ) ^ (j.val + 1) • f (mergeAdjacent g j)) +
    (-1 : ℤ) ^ (n + 1) • f (fun i => g i.castSucc)

/-- Sanity: homogeneous degree zero is precisely the coefficient action. -/
example (a : A) (g : Fin 1 → G) :
    homogeneousTransform 0 (fun _ => a) g = g 0 • a := rfl

/-- Sanity: the explicit differential in degree zero is g.a-a. -/
example (a : A) (g : Fin 1 → G) :
    inhomogeneousDifferential 0 (fun _ => a) g = g 0 • a - a := by
  simp [inhomogeneousDifferential, sub_eq_add_neg]

/-- Sanity: the omitted prefix in degree zero is the empty product, not an
arbitrary group element. -/
example (g : Fin 0 → G) : cumulativeTuple g 0 = 1 := rfl

variable (K : Type*) [RCLike K]
variable {E F : Type*}
variable [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable [AddCommGroup F] [Module K F] [TopologicalSpace F]
variable [TopologicalSpace G] [ChartedSpace E G]
variable [TopologicalSpace A] [ChartedSpace F A]

/-- PDF p. 61, Definition B.2: normalized cochains smooth on an open identity
neighborhood. In degree zero the normalization has no indices, as required. -/
def LocallySmoothCochain (n : ℕ) (f : (Fin n → G) → A) : Prop :=
  (∀ (g : Fin n → G) (i : Fin n), g i = 1 → f g = 0) ∧
    ∃ U : Set (Fin n → G), IsOpen U ∧ (fun _ => 1) ∈ U ∧
      ManifoldSmoothOn K (E := (Fin n → E)) (F := F) U f

end GroupCochains

section CupProducts

variable {G U V W : Type*} [Group G]
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [DistribMulAction G U] [DistribMulAction G V] [DistribMulAction G W]

/-- PDF p. 78: the ordered, action-twisted cup product. The initial block's
product acts on the second cochain, also when either degree is zero. -/
def cupProduct (m : U → V → W) (p q : ℕ)
    (alpha : (Fin p → G) → U) (beta : (Fin q → G) → V)
    (g : Fin (p + q) → G) : W :=
  m (alpha (fun i => g (Fin.castAdd q i)))
    (((List.ofFn (fun i : Fin p => g (Fin.castAdd q i))).prod) •
      beta (fun i => g (Fin.natAdd p i)))

/-- Sanity: a degree-zero first factor produces the untwisted coefficient
pairing; the empty product acts as the identity. -/
example (m : U → V → W) (u : U) (q : ℕ)
    (beta : (Fin q → G) → V) (g : Fin (0 + q) → G) :
    cupProduct m 0 q (fun _ => u) beta g =
      m u (beta (fun i => g (Fin.natAdd 0 i))) := by
  simp [cupProduct]

variable (K : Type*) [RCLike K]
variable {E EU EV EW : Type*}
variable [AddCommGroup E] [Module K E] [TopologicalSpace E]
variable [AddCommGroup EU] [Module K EU] [TopologicalSpace EU]
variable [AddCommGroup EV] [Module K EV] [TopologicalSpace EV]
variable [AddCommGroup EW] [Module K EW] [TopologicalSpace EW]
variable [TopologicalSpace G] [ChartedSpace E G]
variable [TopologicalSpace U] [ChartedSpace EU U]
variable [TopologicalSpace V] [ChartedSpace EV V]
variable [TopologicalSpace W] [ChartedSpace EW W]

end CupProducts

/-- Sanity for the local geometry and cochains: the zero-dimensional singleton
has an actual compatible Lie atlas, and its degree-zero cochain is locally
smooth. No arbitrary smoothness predicate or nonempty-domain assumption is
used to manufacture the example. -/
example :
    LocallyConvexModel ℝ PUnit.{1} ∧
    ScalarAtlas ℝ (E := PUnit.{1}) (M := PUnit.{1}) ∧
    DirectionalLieGroup ℝ PUnit.{1} PUnit.{1} ∧
    DirectionalAddLieGroup ℝ PUnit.{1} PUnit.{1} ∧
    LocallySmoothCochain ℝ (E := PUnit.{1}) (F := PUnit.{1}) 0
      (fun _ : Fin 0 → PUnit.{1} => (0 : PUnit.{1})) := by
  have hs : ∀ {D : Type} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
      (S : Set D) (f : D → PUnit.{1}), ScalarSmoothOn ℝ S f := by
    intro D _ _ _ S f
    dsimp [ScalarSmoothOn]
    constructor
    · refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
      · intro x hx
        exact Subsingleton.elim _ _
      · intro n
        exact continuousOn_const
      · intro n x hx a h
        simpa only [sub_self, smul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
            (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
    · refine ⟨fun _ => 0, ?_⟩
      intro x hx h
      simpa only [sub_self, smul_zero, LinearMap.zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : PUnit.{1}))
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : PUnit.{1})))
  have hm : ∀ {D X : Type} [AddCommGroup D] [Module ℝ D]
      [TopologicalSpace D] [TopologicalSpace X] [ChartedSpace D X]
      (S : Set X) (f : X → PUnit.{1}),
      ManifoldSmoothOn ℝ (E := D) (F := PUnit.{1}) S f := by
    intro D X _ _ _ _ _ S f
    refine ⟨?_, ?_⟩
    · have hf : f = fun _ => PUnit.unit := funext (fun _ => Subsingleton.elim _ _)
      rw [hf]
      exact continuousOn_const
    · intro c hc e he
      exact hs _ _
  have hModel : LocallyConvexModel ℝ PUnit.{1} := by
    refine ⟨inferInstance, inferInstance, inferInstance,
      (inferInstance : Module ℝ PUnit.{1}), ?_⟩
    exact ⟨inferInstance, inferInstance⟩
  have hAtlas : ScalarAtlas ℝ (E := PUnit.{1}) (M := PUnit.{1}) := by
    constructor
    · intro c hc e he
      exact (hs _ _).1
    · intro c hc e he
      exact hs _ _
  refine ⟨hModel, hAtlas, ?_, ?_, ?_⟩
  · exact ⟨hModel, inferInstance, hAtlas, hm Set.univ _, hm Set.univ _⟩
  · exact ⟨hModel, inferInstance, hAtlas, hm Set.univ _, hm Set.univ _⟩
  · refine ⟨?_, Set.univ, isOpen_univ, Set.mem_univ _, hm Set.univ _⟩
    intro g i
    exact Fin.elim0 i

end QAlgorithms.Papers.Independent.Renew46.P29


