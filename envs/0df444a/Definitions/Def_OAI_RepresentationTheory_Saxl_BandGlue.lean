-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
-- name    : OAI_RepresentationTheory_Saxl_BandGlue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:25:05.716666+00:00
-- url     : https://prove2.me/theorems/29e679b2-deaa-4cf8-99b6-f8d0ce57f07f
-- title:
--   Gluing a band intertwiner into a colored orbit map, and coordinate-support subspaces
-- statement:
--   Combining a map valued in colorings of one block with a linear map on that block, and subspaces of vectors with prescribed support.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. Fix a bijection $\theta:[n]\to[a]\sqcup[b]$ splitting the positions into blocks $A$ (size $a$) and $B$ (size $b$), and for a word $w:[n]\to[d]$ let $w^A:[a]\to[d]$ and $w^B:[b]\to[d]$ be its restrictions to the two blocks (read through $\theta^{-1}$).
--
--   1. **Band glue.** Let $X$ be a complex vector space, let $T$ be a linear map from $X$ to the space of functions $[k]^{[b]}\to M_{a,d}$ (so $T(x)$ assigns to every coloring $c:[b]\to[k]$ of the block $B$ a vector $T(x)(c)\in M_{a,d}$), and let $L:M_{b,k}\to M_{b,d}$ be linear. The glued map $X\to M_{n,d}$ is
--   $$
--   \mathrm{glue}_\theta(T,L)(x)(w)=L\big(c\mapsto T(x)(c)(w^{A})\big)(w^{B}).
--   $$
--   For the fixed $A$-word $u=w^A$, the scalars $c\mapsto T(x)(c)(u)$ form a vector of $M_{b,k}$; it is transformed by $L$ and then evaluated at the $B$-word $w^B$. In tensor language, if $T(x)$ is viewed as an element of $M_{a,d}\otimes M_{b,k}$, the glued vector is $(\mathrm{id}\otimes L)(T(x))$ transported to $M_{n,d}$ by $x'\otimes y'\mapsto\big(w\mapsto x'(w^A)\,y'(w^B)\big)$.
--
--   2. **Coordinate-support subspace.** For a property $P$ of words $w:[n]\to[d]$, the complex subspace
--   $$
--   \{x\in M_{n,d}:\ x(w)=0\ \text{for every } w \text{ that does not satisfy } P\},
--   $$
--   the vectors supported on $P$ (no invariance under $\mathfrak S_n$ is built in).
--
--   Gluing combines an orbit map on the high block with an intertwiner on the band block into a map to the word space of all positions; this is how a nonzero map, equivariant for the block permutations, into the cyclic module of a position product is produced. The support subspaces, used with sector conditions on words, record on which words such glued vectors can be nonzero.
--
--   **Formalization Note** The definitions are `bandGlue e T L`, where `e` is the bijection $\theta$, `T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)` and `L : WordSpace b k →ₗ[ℂ] WordSpace b d`, with $w^A,w^B$ given by `leftWord e w` and `rightWord e w`; and `coordinateSub n d P`, a `Submodule ℂ (WordSpace n d)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandGlue.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandGlue.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/
def bandGlue {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) : X →ₗ[ℂ] WordSpace n d where
  toFun x w := L (fun cb => T x cb (leftWord e w)) (rightWord e w)
  map_add' x y := by
    ext w
    simp only [map_add, Pi.add_apply]
    change L ((fun cb => T x cb (leftWord e w)) + (fun cb => T y cb (leftWord e w))) (rightWord e w) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    ext w
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
    change L (c • (fun cb => T x cb (leftWord e w))) (rightWord e w) = _
    rw [map_smul]
    rfl

/- A module containing every band Specht type of the relevant height detects
any nonzero high-valued colored-band vector. No multiplicity hypothesis is needed. -/
def coordinateSub (n d : ℕ) (P : (Fin n → Fin d) → Prop) : Submodule ℂ (WordSpace n d) where
  carrier := {x | ∀ w, ¬ P w → x w = 0}
  zero_mem' := by intro w hw; rfl
  add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
  smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero]

end Saxl

end

end OAI


