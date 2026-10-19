-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
-- name    : OAI_RepresentationTheory_Saxl_PieriRestriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:31:05.504224+00:00
-- url     : https://prove2.me/theorems/c0d2adfb-9216-4c08-875f-0207177fcad4
-- title:
--   Horizontal strips, tableau inclusions and letter-restriction contractions of word spaces
-- statement:
--   Combinatorial and linear ingredients of the horizontal-strip (Pieri) restriction maps between Specht modules.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$. For Young diagrams, $\nu\subseteq\mu$ denotes inclusion of cell sets; $\mu'_j$ is the number of cells of $\mu$ in column $j$, and $\ell(\mu)=\mu'_0$ is the number of rows.
--
--   1. **Horizontal strip.** For Young diagrams $\nu,\mu$, the skew shape $\mu/\nu$ is a horizontal strip when $\nu\subseteq\mu$ and any two cells of $\mu\setminus\nu$ lying in the same column are equal, i.e. $\mu\setminus\nu$ has at most one cell in each column.
--
--   2. **Tableau inclusion.** For tableaux $s:[a]\to\nu$ and $t:[n]\to\mu$ with $\nu\subseteq\mu$, the injection
--   $$
--   \iota_{s,t}:[a]\to[n],\qquad \iota_{s,t}(k)=t^{-1}\big(s(k)\big),
--   $$
--   which sends a position of $s$ to the position of $t$ carrying the same cell; thus $t(\iota_{s,t}(k))=s(k)$.
--
--   3. **Row-letter inclusion.** If $\nu\subseteq\mu$, then $\nu'_j\le\mu'_j$ for every column $j$; in particular $\ell(\nu)\le\ell(\mu)$, and the row-letter inclusion is the embedding $[\ell(\nu)]\to[\ell(\mu)]$, $i\mapsto i$.
--
--   4. **Letter restriction.** For injections $i:[a]\to[n]$ (positions) and $j:[d]\to[e]$ (letters), the linear map $R_{i,j}:M_{n,e}\to M_{a,d}$,
--   $$
--   R_{i,j}(x)(u)=\sum_{\substack{c:[n]\to[e]\\ c\circ i=j\circ u}}x(c),
--   $$
--   which prescribes the letter $j(u(k))$ at the position $i(k)$ and sums over all letters at the remaining positions; it is contraction with the all-ones functional at the deleted positions.
--
--   When $\mu/\nu$ is a horizontal strip, the letter restriction along $\iota_{s,t}$ and the row-letter inclusion, applied to the Specht module of $t$ and followed by the orthogonal projection onto the Specht module of $s$, gives a nonzero linear map that is compatible with every pair of permutations $g\in\mathfrak S_n$, $h\in\mathfrak S_a$ satisfying $g\circ\iota_{s,t}=\iota_{s,t}\circ h$.
--
--   **Formalization Note** The definitions are `HorizontalStrip ν μ`, `tableauInclusion s t h` (an embedding `Fin a ↪ Fin n`, with the lemma `tableauInclusion_cell`), the lemma `colLen_mono`, `rowLetterInclusion h` (given by `Fin.castLEEmb`) and `wordRestrict i j`. Here $\nu\subseteq\mu$ is the order `ν ≤ μ` on `YoungDiagram`, and $\mu'_j$ is `μ.colLen j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PieriRestriction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PieriRestriction.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
def HorizontalStrip (ν μ : YoungDiagram) : Prop :=
  ν ≤ μ ∧ ∀ x ∈ μ, x ∉ ν → ∀ y ∈ μ, y ∉ ν → x.2 = y.2 → x = y

/- Position embedding induced by inclusion of the actual Young diagrams. -/
def tableauInclusion {a n : ℕ} {ν μ : YoungDiagram} (s : Tableau a ν) (t : Tableau n μ)
    (h : ν ≤ μ) : Fin a ↪ Fin n where
  toFun i := t.symm ⟨(s i).val, h (s i).property⟩
  inj' := by
    intro i j hij
    apply s.injective
    apply Subtype.ext
    simpa using congrArg (fun k => (t k).val) hij

lemma colLen_mono {ν μ : YoungDiagram} (h : ν ≤ μ) (j : ℕ) :
    ν.colLen j ≤ μ.colLen j := by
  by_contra hn
  have hm : (μ.colLen j, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hn)
  exact (lt_irrefl _) (YoungDiagram.mem_iff_lt_colLen.mp (h hm))

def rowLetterInclusion {ν μ : YoungDiagram} (h : ν ≤ μ) : Fin (ν.colLen 0) ↪ Fin (μ.colLen 0) :=
  Fin.castLEEmb (colLen_mono h 0)

/- Restrict letters on a specified position set, and sum over all other letters.
This is precisely contraction with the all-ones functional at deleted positions. -/
def wordRestrict {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e) :
    WordSpace n e →ₗ[ℂ] WordSpace a d where
  toFun x b := ∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x c else 0
  map_add' x y := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then x c + y c else 0) =
      (∑ c, if c ∘ i = j ∘ b then x c else 0) + (∑ c, if c ∘ i = j ∘ b then y c else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all
  map_smul' r x := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then r * x c else 0) =
      r * ∑ c, if c ∘ i = j ∘ b then x c else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all

@[simp] lemma tableauInclusion_cell {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin a) :
    (t (tableauInclusion s t h k)).val = (s k).val := by
  change (t (t.symm ⟨(s k).val, h (s k).property⟩)).val = _
  simp

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
end Saxl

end

end OAI


