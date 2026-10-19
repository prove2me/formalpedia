-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
-- name    : OAI_RepresentationTheory_Saxl_SignEquivalence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:27:17.58378+00:00
-- url     : https://prove2.me/theorems/ac11d817-14fd-42d0-8de2-5912c09f80dc
-- title:
--   Transposed tableaux, sign-twisted representations and orbit averages from word spaces
-- statement:
--   Three constructions behind the comparison of a Specht module with the sign twist of the Specht module of the transposed shape.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$. The transpose of $\mu$ is $\mu^{T}=\{(j,i):(i,j)\in\mu\}$.
--
--   1. **Transposed tableau.** For a tableau $t$ of shape $\mu$ on $[n]$, the tableau $t^{T}$ of shape $\mu^{T}$ on the same positions is given by $t^{T}(q)=(j,i)$ whenever $t(q)=(i,j)$.
--
--   2. **Sign twist.** For a representation $\rho$ of $\mathfrak S_n$ on a complex vector space $V$, the representation $\operatorname{sgn}\otimes\rho$ on the same space $V$, $g\mapsto\operatorname{sgn}(g)\,\rho(g)$.
--
--   3. **Orbit average.** For a representation $\rho$ of $\mathfrak S_n$ on $V$, a word $a:[n]\to[d]$ and a vector $y\in V$, the linear map $M_{n,d}\to V$
--   $$
--   x\longmapsto\sum_{g\in\mathfrak S_n}x(a\circ g^{-1})\,\rho(g)\,y .
--   $$
--   It sends $\delta_u$ to $\sum_{g:\,a\circ g^{-1}=u}\rho(g)y$, and it is $\mathfrak S_n$-equivariant for every choice of $y$.
--
--   These are used to prove the sign-conjugacy of Specht modules: the Specht module of $t$ is isomorphic to the sign twist of the Specht module of $t^{T}$, the isomorphism being obtained from an orbit average of the polytabloid of $t^{T}$ along the row word of $t$ (the word sending each position to the row of its cell).
--
--   **Formalization Note** The definitions are `transposeTableau t`, `signTwist ρ` (built from `signC`, the sign character with values in $\mathbb{C}$) and `orbitAverage ρ a y`, a `Representation.IntertwiningMap (wordRep n d) ρ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

def transposeTableau {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Tableau n μ.transpose := t.trans
  { toFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mpr (by simp)⟩
    invFun := fun c => ⟨c.val.swap, YoungDiagram.mem_transpose.mp c.property⟩
    left_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _
    right_inv := by intro c; apply Subtype.ext; exact Prod.swap_swap _ }

/- Twisting by the actual sign character, on the same complex vector space. -/
def signTwist {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Representation ℂ (Equiv.Perm (Fin n)) V where
  toFun g := signC g • ρ g
  map_one' := by simp
  map_mul' g h := by ext x; simp [map_mul, smul_smul, mul_comm]

def orbitAverage {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V) :
    Representation.IntertwiningMap (wordRep n d) ρ where
  toFun x := ∑ g : Equiv.Perm (Fin n), x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y
  map_add' x z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (∑ g : Equiv.Perm (Fin n), x ((a ∘ (g⁻¹ : Equiv.Perm (Fin n))) ∘ h) • ρ g y) =
      ρ h (∑ g : Equiv.Perm (Fin n), x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y)
    simp only [map_sum, map_smul]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change x ((a ∘ ((h * g)⁻¹ : Equiv.Perm (Fin n))) ∘ h) • ρ (h * g) y =
      x (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ h (ρ g y)
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    congr 2
    funext i
    simp

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
end Saxl

end

end OAI


