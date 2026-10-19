-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
-- name    : OAI_GroupTheory_Hyperbolic_Chains
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:02:42.36372+00:00
-- url     : https://prove2.me/theorems/d9ecdc42-84a6-4c16-ab3d-ae3310718b47
-- title:
--   Cellular chains of the Cayley complex of a block presentation
-- statement:
--   Free $\Gamma$-chain modules and boundary maps for the triangle complex of a block presentation with group $\Gamma$.
--
--   1. **Free chains.** For a set $A$ and a group $G$, the free chains are finitely supported functions $A\times G\to\mathbb Z$; left translation by $g$ sends $(a,h)\mapsto(a,gh)$ and is a linear automorphism. For $\Gamma$ the presented group, $C_0$, $C_1$ and $C_2$ are the free chains on the vertices $o,v,w$, on the edges, and on the positive faces. A positive face is a triangle face $(a,b,c)$ whose sides end at $v$, $w$, $o$ respectively.
--   2. **Edge chains.** A lifted oriented edge $(e,g)$ gives $+[e,g]$ if $e$ is positively oriented and $-[\bar e,g']$ otherwise, where $(\bar e,g')$ is its flip; flipping negates the chain. A lifted word gives the sum of its edge chains.
--   3. **Boundaries.** The edge $[e,g]$ with generator $\gamma_e$ has
--   $$
--   \partial_1[e,g]=[\mathrm{target}(e),g]-[\mathrm{source}(e),g\gamma_e^{-1}],
--   $$
--   and $\partial_2$ sends a positive face at $g$ to the sum of the edge chains of its three lifted sides.
--   4. **Face evaluation.** The positive atom of $(a,b,c)$ is the basis element of $C_2$ at the group coordinate of $c$ when $(a,b,c)$ is a positive face, and $0$ otherwise. The ordered evaluation subtracts the atom of the reversed flipped triple $(\bar c,\bar b,\bar a)$, and the face evaluation sums the ordered evaluations over the three cyclic rotations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Chains.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Chains.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

/-- The free integral module on copies of the regular left group action. -/
abbrev FreeChain (A G : Type) := (A × G) →₀ ℤ

noncomputable def chainShift {A G : Type} [Group G] (g : G) :
    FreeChain A G ≃ₗ[ℤ] FreeChain A G :=
  Finsupp.domLCongr (Equiv.prodCongr (Equiv.refl A) (Equiv.mulLeft g))

@[simp] theorem chainShift_single {A G : Type} [Group G] (g : G) (a : A) (h : G) (n : ℤ) :
    chainShift g (Finsupp.single (a,h) n) = Finsupp.single (a,g*h) n :=
  Finsupp.domLCongr_single _ _ _

namespace BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev C₀ := FreeChain d.Vertex d.GroupType
abbrev C₁ := FreeChain d.Edge d.GroupType

def PositiveFace (t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge) : Prop :=
  d.TriangleFace t.1 t.2.1 t.2.2 ∧ d.edgeTarget t.1 = .v ∧
    d.edgeTarget t.2.1 = .w ∧ d.edgeTarget t.2.2 = .o

abbrev FaceBase := {t : d.OrientedEdge × d.OrientedEdge × d.OrientedEdge // d.PositiveFace t}
abbrev C₂ := FreeChain d.FaceBase d.GroupType

/-- An oriented edge is represented in a free module on the positive orientations. -/
noncomputable def edgeChain (e : d.LiftedEdge) : d.C₁ :=
  if e.1.2 then Finsupp.single (e.1.1,e.2) 1 else
    -Finsupp.single (e.1.1,(d.liftedFlip e).2) 1

@[simp] theorem edgeChain_flip (e : d.LiftedEdge) :
    d.edgeChain (d.liftedFlip e) = -d.edgeChain e := by
  rcases e with ⟨⟨e,s⟩,g⟩
  cases s <;> simp [edgeChain,liftedFlip,flipEdge,edgeValue]

noncomputable def boundary₁ : d.C₁ →ₗ[ℤ] d.C₀ :=
  Finsupp.linearCombination ℤ (fun e =>
    Finsupp.single (d.edgeTarget (e.1,true), e.2) 1 -
      Finsupp.single (d.edgeTarget (d.flipEdge (e.1,true)),e.2*(d.edge (e.1))⁻¹) 1)

noncomputable def boundary₂ : d.C₂ →ₗ[ℤ] d.C₁ :=
  Finsupp.linearCombination ℤ (fun t =>
    d.edgeChain (t.1.val.1,t.2*d.edgeValue t.1.val.1) +
      d.edgeChain (t.1.val.2.1,t.2*d.edgeValue t.1.val.1*d.edgeValue t.1.val.2.1) +
        d.edgeChain (t.1.val.2.2,t.2))

/-- The positively oriented, O-based atom. Nonfaces give zero. -/
noncomputable def positiveAtom (a b c : d.LiftedEdge) : d.C₂ :=
  if h : d.PositiveFace (a.1,b.1,c.1) then Finsupp.single (⟨(a.1,b.1,c.1),h⟩,c.2) 1 else 0

/-- Exactly one O-corner, with its orientation sign. -/
noncomputable def orderedEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.positiveAtom a b c - d.positiveAtom (d.liftedFlip c) (d.liftedFlip b) (d.liftedFlip a)

/-- Cyclic evaluation of one oriented face. -/
noncomputable def faceEval (a b c : d.LiftedEdge) : d.C₂ :=
  d.orderedEval a b c + d.orderedEval b c a + d.orderedEval c a b

end BlockPresentation
end Release075

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

noncomputable def wordChain (w : List d.LiftedEdge) : d.C₁ := (w.map d.edgeChain).sum

end Release075.BlockPresentation

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI


