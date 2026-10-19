-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
-- name    : OAI_RepresentationTheory_Saxl_RepeatedProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:40:15.382147+00:00
-- url     : https://prove2.me/theorems/9afe5ff9-102d-41a8-b930-2024f0ffc344
-- title:
--   Content orbits of words, orbit projections and the letter-sum map on word spaces
-- statement:
--   Fix $n,d\in\mathbb{N}$, write $[d]=\{0,\dots,d-1\}$, and let $W_{n,d}$ be the space of functions $x$ on words $c:[n]\to[d]$, with basis vectors $e_c$ and with the symmetric group $S_n$ acting by permuting positions, $(g\cdot x)(c)=x(c\circ g)$. This is the $n$-fold tensor power of $\mathbb{C}^d$ written in coordinates.
--
--   1. **Content orbit.** For words $t,c:[n]\to[d]$, $c$ lies in the orbit of $t$ if $c=t\circ g$ for some $g\in S_n$, i.e. $c$ is a rearrangement of $t$ (every letter occurs equally often in both). The relation is invariant under rearranging $c$: $c\circ g$ lies in the orbit of $t$ if and only if $c$ does.
--   2. **Orbit projection.** For a word $t$, the coordinate projection $P_t:W_{n,d}\to W_{n,d}$,
--   $$(P_tx)(c)=\begin{cases}x(c)&\text{if }c\text{ is a rearrangement of }t,\\ 0&\text{otherwise,}\end{cases}$$
--   keeps exactly the coordinates on the $S_n$-orbit of $t$. Since that orbit is $S_n$-stable, $P_t$ is an intertwiner of $S_n$-representations; its image is the permutation module spanned by the $e_c$ with $c$ a rearrangement of $t$.
--   3. **Letter-sum map.** Read a word over the alphabet $[d]\times[d]$ (encoded as $[d^2]$) as a pair of words $(a,b)$. For $e\in\mathbb{N}$ the map $\Sigma:W_{n,d^2}\to W_{n,e}$ is the $n$-th tensor power of the letter map $e_{(\alpha,\beta)}\mapsto e_{\alpha+\beta}$ (and $e_{(\alpha,\beta)}\mapsto0$ when $\alpha+\beta\ge e$):
--   $$(\Sigma x)(c)=\sum_{(a,b)}x(a,b)\prod_{p\in[n]}\mathbf{1}\bigl[a(p)+b(p)=c(p)\bigr].$$
--   On basis vectors, $\Sigma e_{(a,b)}=e_{a+b}$ if $a(p)+b(p)<e$ for every position $p$, and $\Sigma e_{(a,b)}=0$ otherwise. It is an intertwiner because it acts letter by letter.
--
--   Composing the letter-sum map with an orbit projection extracts, from a vector of the tensor square $W_{n,d}\otimes W_{n,d}\cong W_{n,d^2}$, its component on words of one prescribed content. This is how a specific permutation-module generator is detected inside the tensor square of a staircase Specht module.
--
--   **Formalization Note** The relation is `wordOrbit t c`, with invariance lemma `wordOrbit_perm`; `orbitProjection t` is `coordinateProjection (wordOrbit t)` packaged as an intertwiner, and `pairSumMap n d e` is `wordMap` applied to the letter kernel $L((\alpha,\beta),\gamma)=\mathbf{1}[\alpha+\beta=\gamma]$, with pairs encoded by `finProdFinEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

def wordOrbit {n d : ℕ} (t : Fin n → Fin d) (c : Fin n → Fin d) : Prop :=
  ∃ g : Equiv.Perm (Fin n), c = t ∘ g

lemma wordOrbit_perm {n d : ℕ} (t c : Fin n → Fin d) (g : Equiv.Perm (Fin n)) :
    wordOrbit t (c ∘ g) ↔ wordOrbit t c := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h*g⁻¹, ?_⟩
    funext i
    have he := congrFun hh (g⁻¹ i)
    simpa using he
  · rintro ⟨h, rfl⟩
    exact ⟨h*g, rfl⟩

def orbitProjection {n d : ℕ} (t : Fin n → Fin d) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n d) where
  toLinearMap := coordinateProjection (wordOrbit t)
  isIntertwining' g := by
    classical
    apply LinearMap.ext
    intro x
    ext c
    change (if wordOrbit t c then x (c ∘ g) else 0) =
      (if wordOrbit t (c ∘ g) then x (c ∘ g) else 0)
    rw [wordOrbit_perm]

def pairSumMap (n d e : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n e) :=
  wordMap (fun a c => if (finProdFinEquiv.symm a).1.val +
    (finProdFinEquiv.symm a).2.val = c.val then 1 else 0)

end Saxl

end

end OAI


