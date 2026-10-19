-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport
-- name    : OAI_RepresentationTheory_Saxl_DominatedSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:52:02.628753+00:00
-- url     : https://prove2.me/theorems/c9e43967-5dfb-47da-9ce0-5cffb2804c23
-- title:
--   Column truncation, self-conjugacy of the staircase and cancelling a sign twist
-- statement:
--   This file collects three small constructions used when comparing a Young diagram with its conjugate. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under moving up or left, and $\mu^{\mathsf T}=\{(j,i):(i,j)\in\mu\}$ is its conjugate (transpose).
--
--   1. **Column truncation.** For $k\in\mathbb{N}$,
--   $$\operatorname{col}_{<k}(\mu)=\bigl((\mu^{\mathsf T})_{<k}\bigr)^{\mathsf T}=\{(i,j)\in\mu : j<k\},$$
--   the diagram formed by the first $k$ columns of $\mu$, obtained by truncating the conjugate to its first $k$ rows and conjugating back.
--   2. **The staircase is self-conjugate.** For every $m\in\mathbb{N}$ the staircase $\delta_m=\{(i,j):i+j<m\}$ satisfies $\delta_m^{\mathsf T}=\delta_m$.
--   3. **Cancelling a sign twist.** For representations $\rho,\sigma$ of the symmetric group $S_n$ on complex vector spaces, write $\operatorname{sgn}\otimes\rho$ for the representation $g\mapsto\operatorname{sgn}(g)\rho(g)$ on the same space. Every intertwiner $f:\operatorname{sgn}\otimes\rho\to\sigma$ is, as the same linear map, an intertwiner $\rho\to\operatorname{sgn}\otimes\sigma$: from $f(\operatorname{sgn}(g)\rho(g)x)=\sigma(g)f(x)$ and $\operatorname{sgn}(g)^2=1$ one gets
--   $$f(\rho(g)x)=\operatorname{sgn}(g)\,\sigma(g)f(x)\qquad(g\in S_n).$$
--
--   Column truncation is used in the proof that conjugation reverses the dominance order, and together with the self-conjugacy of $\delta_m$ this turns "$\mu$ is dominated by $\delta_m$" into "$\mu^{\mathsf T}$ dominates $\delta_m$". The sign-cancelling map converts an intertwiner out of the sign-twisted staircase cyclic module into one out of the cyclic module itself. These steps are used to show that every Specht module whose shape is dominated by the staircase occurs in the cyclic staircase module.
--
--   **Formalization Note** The items are `colTruncate μ k`, the simp lemma `staircase_transpose` and `signCancelMap`; the conjugate is Mathlib's `YoungDiagram.transpose`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

def colTruncate (μ : YoungDiagram) (k : ℕ) := (rowTruncate μ.transpose k).transpose

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
open scoped MonoidAlgebra

end Saxl

namespace Saxl

@[simp] lemma staircase_transpose (m : ℕ) : (staircase m).transpose = staircase m := by
  apply YoungDiagram.ext
  apply Finset.ext
  intro x
  rcases x with ⟨i,j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_staircase]
  omega

def signCancelMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap (signTwist ρ) σ) :
    Representation.IntertwiningMap ρ (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (ρ g x) = signC g • σ g (f x)
    have hh := LinearMap.congr_fun (f.isIntertwining' g) x
    change f (signC g • ρ g x) = σ g (f x) at hh
    have he := congrArg (fun y => signC g • y) hh
    rw [map_smul, smul_smul, signC_mul_self, one_smul] at he
    exact he

end Saxl

end

end OAI


