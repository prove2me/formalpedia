-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
-- name    : OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:40:36.857886+00:00
-- url     : https://prove2.me/theorems/a7a878ef-29e4-4700-9fdb-17559a30b9c1
-- title:
--   The Foulkes–Howe formula as a multilinear function of a single row
-- statement:
--   Let $V$ be a complex vector space and $S(V)$ its symmetric algebra over $\mathbb{C}$. For $n\in\mathbb{N}$, $\mathrm{Sym}^nV$ denotes the $\mathbb{C}$-linear span inside $S(V)$ of all products $u_0u_1\cdots u_{n-1}$ of $n$ vectors of $V$, and for $u_0,\dots,u_{n-1}\in V$ we write $[u_0,\dots,u_{n-1}]\in\mathrm{Sym}^nV$ for this product. For natural numbers $a,b$ and a grid $v=(v_{j,i})_{0\le j<b,\ 0\le i<a}$ of vectors of $V$, the Foulkes–Howe formula is
--   $$
--   F(v)=\frac{1}{(a!)^{b}}\sum_{(\sigma_0,\dots,\sigma_{b-1})\in S_a^{\,b}}\bigl[\,w^\sigma_0,\dots,w^\sigma_{a-1}\,\bigr]\in\mathrm{Sym}^a(\mathrm{Sym}^bV),\qquad w^\sigma_i=\bigl[v_{0,\sigma_0(i)},\dots,v_{b-1,\sigma_{b-1}(i)}\bigr],
--   $$
--   where $S_a$ is the symmetric group on $\{0,\dots,a-1\}$ and the outer bracket is the product of $a$ elements of $\mathrm{Sym}^bV$ in the symmetric algebra of $\mathrm{Sym}^bV$.
--
--   The module defines:
--
--   1. **Fibre reindexing.** For sets $I,J$ and an element $i\in I$, the bijection between the fibre $\{(i',j)\in I\times J : i'=i\}$ and $J$ that sends $(i,j)$ to $j$.
--   2. **Row form.** For a grid $v$ and a row index $j<b$, the map
--   $$
--   R_{v,j}\colon V^a\to\mathrm{Sym}^a(\mathrm{Sym}^bV),\qquad R_{v,j}(u_0,\dots,u_{a-1})=F\bigl(v[j\leftarrow u]\bigr),
--   $$
--   where $v[j\leftarrow u]$ is the grid obtained from $v$ by replacing its $j$-th row by $u=(u_0,\dots,u_{a-1})$ and keeping every other row. It is a multilinear map in $u_0,\dots,u_{a-1}$, obtained from the multilinear version of $F$ by freezing all entries outside row $j$; its value formula is recorded as a lemma.
--
--   Since $F$ does not change when the entries inside one row are permuted, $R_{v,j}$ is a symmetric multilinear map and therefore descends to a linear map on $\mathrm{Sym}^aV$. This row-by-row linearity is what allows the formula, prescribed only on products of monomials, to be extended to a linear map $\mathrm{Sym}^b(\mathrm{Sym}^aV)\to\mathrm{Sym}^a(\mathrm{Sym}^bV)$.
--
--   **Formalization Note** `foulkesRowFormSpanning a b V v j` is built from `foulkesMultilinear` by `MultilinearMap.domDomRestrict` to the coordinates in row `j` (the others fixed to the entries of `v`) followed by reindexing along `rowIndexEquiv j`; `foulkesRowFormSpanning_apply` states that its value at `u` is `foulkesFormula a b V (Function.update v j u)`. No finite-dimensionality of $V$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/CanonicalMap.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/CanonicalMap.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear

namespace OAI

noncomputable section
namespace Problem346

 def rowIndexEquiv {I J : Type*} (i : I) :
    {p : I × J // p.1 = i} ≃ J where
  toFun p := p.1.2
  invFun j := ⟨(i, j), rfl⟩
  left_inv := by
    rintro ⟨⟨i', j⟩, h⟩
    simp only at h
    subst i'
    rfl
  right_inv _ := rfl

/-- Hold all but a single input row of the Foulkes formula fixed. -/
def foulkesRowFormSpanning (a b : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (v : Fin b → Fin a → V) (j : Fin b) :
    MultilinearMap ℂ (fun _ : Fin a => V) (SymPow a (SymPow b V)) := by
  classical
  exact ((foulkesMultilinear a b V).domDomRestrict
    (fun p : Fin b × Fin a => p.1 = j) (fun p => v p.1.1 p.1.2)).domDomCongr
      (rowIndexEquiv j)

@[simp] theorem foulkesRowFormSpanning_apply (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin a → V) (j : Fin b)
    (u : Fin a → V) :
    foulkesRowFormSpanning a b V v j u =
      foulkesFormula a b V (Function.update v j u) := by
  classical
  change foulkesMultilinear a b V
    (fun p => if h : p.1 = j then u p.2 else v p.1 p.2) = _
  rw [foulkesMultilinear_apply]
  congr 1
  funext k i
  by_cases h : k = j
  · subst k
    simp
  · simp [h]

end Problem346

end

end OAI


