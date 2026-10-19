-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
-- name    : OAI_RepresentationTheory_Saxl_StaircaseSign
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:42:31.664471+00:00
-- url     : https://prove2.me/theorems/9f053ef6-955e-4aa3-82f6-0a253e7db944
-- title:
--   Row reversal, the repeated target word and sign twists for the staircase Specht module
-- statement:
--   Fix $m\in\mathbb{N}$ and let $\delta_m=\{(i,j)\in\mathbb{N}^2 : i+j<m\}$ be the staircase diagram; row $i$ consists of the cells $(i,0),\dots,(i,m-1-i)$, and $\delta_m$ has $n=m(m+1)/2$ cells and $m$ rows. Let $T$ be the fixed canonical tableau of $\delta_m$ (a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells), $T'$ the transposed tableau ($T'(p)$ is the transpose of $T(p)$), $e_T$ the polytabloid of $T$ in the word space $W_{n,m}$ of functions on words $[n]\to[m]$ (on which $S_n$ acts by $(g\cdot x)(a)=x(a\circ g)$), and $S^{\delta_m}$ the Specht module spanned by the $S_n$-orbit of $e_T$. The column group $C_{T'}$ consists of the permutations of positions that preserve the column of $T'$, i.e. the row of $T$.
--
--   1. **Row reversal.** The involution $r_m(i,j)=(i,\,m-1-i-j)$ of $\delta_m$ reverses each row, and $\varrho_m=T^{-1}\circ r_m\circ T\in S_n$ is the corresponding permutation of positions. It preserves the rows of $T$, so $\varrho_m\in C_{T'}$; for every position $p$ the column indices of $T(p)$ and $T(\varrho_m(p))$ add up to $m-1-i$, where $i$ is the row of $T(p)$.
--   2. **Repeated target word.** $\tau_m:[n]\to[m]$, $\tau_m(p)=m-1-i$ when $T(p)$ lies in row $i$. It is the row word of $T$ with the letters reversed, and letter $\ell$ occurs exactly $\ell+1$ times, so $\tau_m$ has content $(1,2,\dots,m)$.
--   3. **Row average.** The vector
--   $$\bar e_T=\sum_{g\in C_{T'}} g\cdot e_T\in S^{\delta_m},$$
--   the sum of the polytabloid over the row-preserving permutations of $T$.
--   4. **Sign twist of an intertwiner.** For a representation $\rho$ of $S_n$, $\operatorname{sgn}\otimes\rho$ is the representation $g\mapsto\operatorname{sgn}(g)\rho(g)$ on the same space. Any intertwiner $f:\rho\to\sigma$ is, as the same linear map, an intertwiner $\operatorname{sgn}\otimes\rho\to\operatorname{sgn}\otimes\sigma$.
--   5. **Moving a sign across a tensor product.** For representations $\rho,\sigma,\tau$ of $S_n$ on spaces $X,Y,Z$ and an intertwiner $f:\sigma\to\operatorname{sgn}\otimes\tau$, the map $\mathrm{id}_X\otimes f$ is an intertwiner
--   $$\operatorname{sgn}\otimes(\rho\otimes\sigma)\longrightarrow\rho\otimes\tau$$
--   for the diagonal actions, because $\operatorname{sgn}(g)^2=1$.
--
--   The staircase is self-conjugate, and these objects serve to use an isomorphism $S^{\delta_m}\cong\operatorname{sgn}\otimes S^{\delta_m}$ concretely through the two tableaux $T$ and $T'$: the row average $\bar e_T$ is the vector on which such an isomorphism is evaluated, the row reversal $\varrho_m$ pairs complementary columns within each row, and $\tau_m$ is the target word whose orbit projection detects words of content $(1,2,\dots,m)$ in the tensor square.
--
--   **Formalization Note** The items are `rowReversalCell`, `rowReversalEquiv`, `rowReversal m` (an element of `columnGroup (stairRowTableau m)`), `repeatedTarget m` (defined with `Fin.rev` of the row word), `rowAverage m`, `signTwistMap` and `tensorAnti`; `rowReversalCell_involutive` records that $r_m$ is an involution. The cell formula uses natural-number subtraction, which is exact because $i+j<m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StaircaseSign.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StaircaseSign.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

def rowReversalCell (m : ℕ) (x : (staircase m).cells) : (staircase m).cells :=
  ⟨(x.val.1, m-1-x.val.1-x.val.2), by
    have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
    apply mem_staircase.mpr
    omega⟩

lemma rowReversalCell_involutive (m : ℕ) : Function.Involutive (rowReversalCell m) := by
  intro x
  have hx : x.val.1 + x.val.2 < m := mem_staircase.mp x.property
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change m-1-x.val.1-(m-1-x.val.1-x.val.2) = x.val.2
    omega

def rowReversalEquiv (m : ℕ) : Equiv.Perm (staircase m).cells :=
  ⟨rowReversalCell m, rowReversalCell m, rowReversalCell_involutive m, rowReversalCell_involutive m⟩

def rowReversal (m : ℕ) : columnGroup (stairRowTableau m) :=
  ⟨((stairTableau m).trans (rowReversalEquiv m)).trans (stairTableau m).symm, by
    intro i
    change (stairTableau m ((stairTableau m).symm (rowReversalEquiv m (stairTableau m i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def repeatedTarget (m : ℕ) : Fin (staircase m).card → Fin ((staircase m).colLen 0) :=
  fun i => Fin.rev (rowWord (stairTableau m) i)

def rowAverage (m : ℕ) : Specht (stairTableau m) := by
  classical
  letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
  exact ∑ g : columnGroup (stairRowTableau m),
    spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩

def signTwistMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (signTwist ρ) (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (signC g • ρ g x) = signC g • σ g (f x)
    rw [map_smul, f.isIntertwining]

/- A sign intertwiner in the second factor twists the diagonal product. -/
def tensorAnti {n : ℕ} {X : Type uX} {Y : Type uY} {Z : Type uZ} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y} {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (f : Representation.IntertwiningMap σ (signTwist τ)) :
    Representation.IntertwiningMap (signTwist (ρ.tprod σ)) (ρ.tprod τ) where
  toLinearMap := TensorProduct.map LinearMap.id f.toLinearMap
  isIntertwining' g := by
    ext x y
    change TensorProduct.map LinearMap.id f.toLinearMap
      (signC g • (ρ g x ⊗ₜ[ℂ] σ g y)) = ρ g x ⊗ₜ[ℂ] τ g (f y)
    rw [map_smul, TensorProduct.map_tmul]
    change signC g • (ρ g x ⊗ₜ[ℂ] f (σ g y)) = _
    rw [f.isIntertwining]
    change signC g • (ρ g x ⊗ₜ[ℂ] (signC g • τ g (f y))) = _
    rw [TensorProduct.tmul_smul, smul_smul, signC_mul_self, one_smul]

end Saxl

end

end OAI


