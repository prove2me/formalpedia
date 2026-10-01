-- Prove2me | Definitions.Def_AnosovPlugs_Gluing
-- name    : AnosovPlugs_Gluing
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T01:53:43.078902+00:00
-- url     : https://prove2.me/theorems/3d81997d-f004-4f05-bd71-ba65c90cde9e
-- title:
--   Anosov plugs V: glued manifolds, strong isotopy, combinatorial transitivity
-- statement:
--   1. **Self-gluing** (§1.3). $(N,Z)$ is $U/\varphi$ with the vector field induced by $X$ if there is a surjective C¹ immersion $q:U\to N$ with $q(x)=q(y)$ iff $x=y$ or one of them lies in $\partial^{out}U$ and is sent to the other by $\varphi$, and $Dq_x(X(x))=Z(q(x))$ for all $x$.
--   2. **Gluing of two plugs** (Proposition 1.1). $(W,Z)$ is $(U\sqcup V)/\varphi$ (gluing $T^{out}\subseteq\partial^{out}U$ to $T^{in}\subseteq\partial^{in}V$) if there are C¹ embeddings $i_U,i_V$ into $W$ covering $W$, with $i_U(x)=i_V(y)$ iff $x\in T^{out}$ and $y=\varphi(x)$, mapping $X$ and $Y$ to $Z$.
--   3. **Strong isotopy** (Definition 3.28). $(U,X_0,\varphi_0)$ and $(U,X_1,\varphi_1)$ are strongly isotopic if they are joined by a path $(X_t,\varphi_t)_{t\in[0,1]}$ of hyperbolic plugs with filling MS laminations and strongly transverse gluing maps, the vector fields varying continuously in the C¹ topology and the gluing maps continuously.
--   4. **Basic pieces**: nonempty closed invariant subsets of the nonwandering set $\Omega$, open in $\Omega$, with a dense orbit.
--   5. **Combinatorial transitivity** (§1.3). The oriented graph $P$ has the basic pieces as vertices and an edge $\Lambda_i\to\Lambda_j$ if $W^u(\Lambda_i)$ meets $W^s(\Lambda_j)$ or $\varphi(W^u(\Lambda_i)\cap\partial^{out}U)$ meets $W^s(\Lambda_j)\cap\partial^{in}U$. $(U,X,\varphi)$ is combinatorially transitive if $P$ is strongly connected.
--
--   **Formalization Note** The paper writes "$W^u_X(\Lambda_j)\cap\partial^{in}U$" in the second edge condition; since unstable sets do not meet the entrance boundary, this is read as $W^s_X(\Lambda_j)$. "Any two edges" in the paper's definition of strong connectedness is read as "any two vertices". The glued manifold is characterised by these maps rather than built as a quotient type; the vector field $Z$ is not required to be C¹ (the induced field is only continuous for some smooth structures when $X,\varphi$ are only C¹).
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, Proposition 1.1 (p. 1839), §1.3 (pp. 1841–1842), Lemma 3.27 and Definition 3.28 (p. 1862)

import Mathlib
import Definitions.Def_AnosovPlugs_Laminations

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Glued manifolds and induced vector fields (Proposition 1.1, §1.3, Lemma 3.27), strong isotopy
(§1.3, Definition 3.28), basic pieces and combinatorial transitivity (§1.3).
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace AnosovPlugs

variable {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
  [IsManifold I3 ∞ U]
variable {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
  [IsManifold I3 ∞ N]

/-- `(N, Z)` is the manifold `U/φ` obtained from `U` by gluing the exit boundary of `X` to the
entrance boundary by `φ`, endowed with the vector field induced by `X`: the map `q : U → N` is
a surjective C¹ immersion identifying exactly the points `x ∈ ∂^{out} U` with `φ x`, and it
maps `X` to `Z` (`Dq_x (X x) = Z (q x)` for all `x`). -/
def IsSelfGluing (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (Z : (y : N) → TangentSpace I3 y) (q : U → N) : Prop :=
  ContMDiff I3 I3 1 q ∧ (∀ x, Injective (mfderiv I3 I3 q x)) ∧ Surjective q ∧
    (∀ x y, q x = q y ↔
      (x = y ∨ (x ∈ outBoundary X ∧ y = φ x) ∨ (y ∈ outBoundary X ∧ x = φ y))) ∧
    ∀ x, mfderiv I3 I3 q x (X x) = Z (q x)

variable {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
  [IsManifold I3 ∞ V]
variable {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
  [IsManifold I3 ∞ W]

/-- `(W, Z)` is the manifold `(U ⊔ V)/φ` obtained by gluing `T^{out} ⊆ ∂^{out} U` to
`T^{in} ⊆ ∂^{in} V` by `φ`, with the vector field induced by `X` and `Y`: `iU : U → W` and
`iV : V → W` are C¹ embeddings (topological embeddings with injective derivatives), their images
cover `W`, `iU x = iV y` exactly when `x ∈ T^{out}` and `y = φ x`, and they map `X`, `Y`
to `Z`. -/
def IsPlugGluing (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (Tout : Set U) (φ : U → V) (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W) :
    Prop :=
  ContMDiff I3 I3 1 iU ∧ ContMDiff I3 I3 1 iV ∧
    Topology.IsEmbedding iU ∧ Topology.IsEmbedding iV ∧
    (∀ x, Injective (mfderiv I3 I3 iU x)) ∧ (∀ y, Injective (mfderiv I3 I3 iV y)) ∧
    range iU ∪ range iV = univ ∧
    (∀ x y, iU x = iV y ↔ (x ∈ Tout ∧ y = φ x)) ∧
    (∀ x, mfderiv I3 I3 iU x (X x) = Z (iU x)) ∧
    (∀ y, mfderiv I3 I3 iV y (Y y) = Z (iV y))

/-- Definition 3.28: `(U, X₀, φ₀)` and `(U, X₁, φ₁)` are strongly isotopic: there is a path
`(X_t, φ_t)_{t ∈ [0,1]}` from `(X₀, φ₀)` to `(X₁, φ₁)` (the gluing maps agreeing on the exit
boundaries) such that each `(U, X_t)` is a hyperbolic plug with filling MS laminations and each
`φ_t` a strongly transverse gluing diffeomorphism for it; the path of vector fields is continuous
for the C¹ topology (the tangent maps of the sections `x ↦ X_t x` depend continuously on
`(t, v)`), and `(t, x) ↦ φ_t x` is continuous on `{(t, x) | t ∈ [0,1], x ∈ ∂^{out}_{X_t} U}`. -/
def StronglyIsotopic (X₀ : (x : U) → TangentSpace I3 x) (φ₀ : U → U)
    (X₁ : (x : U) → TangentSpace I3 x) (φ₁ : U → U) : Prop :=
  ∃ (Xt : ℝ → (x : U) → TangentSpace I3 x) (φt : ℝ → U → U),
    Xt 0 = X₀ ∧ Xt 1 = X₁ ∧ (∀ x ∈ outBoundary X₀, φt 0 x = φ₀ x) ∧
    (∀ x ∈ outBoundary X₁, φt 1 x = φ₁ x) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, IsFillingHyperbolicPlug (Xt t) ∧ IsStronglyTransverseGluing (Xt t) (φt t)) ∧
    ContinuousOn (fun p : ℝ × TangentBundle I3 U =>
        tangentMap I3 I3.tangent (fun x => (⟨x, Xt p.1 x⟩ : TangentBundle I3 U)) p.2)
      (Icc 0 1 ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × U => φt p.1 p.2) {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ outBoundary (Xt p.1)}

/-- The nonwandering set of `X`: points `x` such that for every neighbourhood `O` of `x` and
every `T`, some orbit segment of duration `t ≥ T` starts and ends in `O`. -/
def nonwanderingSet (X : (x : U) → TangentSpace I3 x) : Set U :=
  {x | ∀ O ∈ 𝓝 x, ∀ T : ℝ, ∃ t ≥ T, ∃ y ∈ O, FlowDefined X y t ∧ flowMap X t y ∈ O}

/-- A basic piece of `X`: a nonempty closed invariant subset of the nonwandering set `Ω`, open in
`Ω`, with a dense orbit (for hyperbolic plugs these are exactly the pieces of the spectral
decomposition of `Ω`). -/
def IsBasicPiece (X : (x : U) → TangentSpace I3 x) (B : Set U) : Prop :=
  B.Nonempty ∧ B ⊆ nonwanderingSet X ∧ IsClosed B ∧
    (∃ O : Set U, IsOpen O ∧ O ∩ nonwanderingSet X = B) ∧
    (∀ x ∈ B, ∀ t : ℝ, flowMap X t x ∈ B) ∧
    ∃ x ∈ B, B ⊆ closure (range fun t : ℝ => flowMap X t x)

/-- The stable set `W^s_X(B)` of `B`: points whose forward orbit is defined for all times and
accumulates only on `B` (converges to `B`). -/
def stableSetOf (X : (x : U) → TangentSpace I3 x) (B : Set U) : Set U :=
  {x | x ∈ stableSet X ∧ Tendsto (fun t : ℝ => flowMap X t x) atTop (𝓝ˢ B)}

/-- The unstable set `W^u_X(B)` of `B`. -/
def unstableSetOf (X : (x : U) → TangentSpace I3 x) (B : Set U) : Set U :=
  {x | x ∈ unstableSet X ∧ Tendsto (fun t : ℝ => flowMap X t x) atBot (𝓝ˢ B)}

/-- Edges of the oriented graph `P` of §1.3: from `B` to `B'` if `W^u_X(B)` meets `W^s_X(B')`,
or if `φ(W^u_X(B) ∩ ∂^{out} U)` meets `W^s_X(B') ∩ ∂^{in} U`. -/
def PieceEdge (X : (x : U) → TangentSpace I3 x) (φ : U → U) (B B' : Set U) : Prop :=
  IsBasicPiece X B ∧ IsBasicPiece X B' ∧
    ((unstableSetOf X B ∩ stableSetOf X B').Nonempty ∨
      (φ '' (unstableSetOf X B ∩ outBoundary X) ∩ (stableSetOf X B' ∩ inBoundary X)).Nonempty)

/-- `(U, X, φ)` is combinatorially transitive: the graph `P` is strongly connected. -/
def IsCombinatoriallyTransitive (X : (x : U) → TangentSpace I3 x) (φ : U → U) : Prop :=
  ∀ B B', IsBasicPiece X B → IsBasicPiece X B' → Relation.ReflTransGen (PieceEdge X φ) B B'

end AnosovPlugs


