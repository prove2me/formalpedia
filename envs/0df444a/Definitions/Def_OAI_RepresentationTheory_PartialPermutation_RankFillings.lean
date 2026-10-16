-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
-- name    : OAI_RepresentationTheory_PartialPermutation_RankFillings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:27:18.774879+00:00
-- url     : https://prove2.me/theorems/e71f04a7-01f3-446c-a78e-f0be66e3cb19
-- title:
--   Permutation of a set assembled from permutations of the fibres of a map
-- statement:
--   Let $\alpha$ and $\iota$ be arbitrary types and let $r:\alpha\to\iota$ be a map. For $i\in\iota$ write $\alpha_i=r^{-1}(i)=\{a\in\alpha : r(a)=i\}$ for the fibre of $r$ over $i$, so that $\alpha$ is the disjoint union of the fibres $\alpha_i$.
--
--   Given a family $p=(p_i)_{i\in\iota}$ of permutations $p_i\in\mathrm{Sym}(\alpha_i)$, one for each fibre, the *fibrewise permutation* $\sigma_{r,p}\in\mathrm{Sym}(\alpha)$ is the permutation of $\alpha$ that acts on every fibre by the prescribed permutation:
--
--   $$
--   \sigma_{r,p}(a)=p_{r(a)}(a)\qquad(a\in\alpha).
--   $$
--
--   It is obtained by transporting the permutation $\coprod_i p_i$ of the disjoint union $\coprod_{i\in\iota}\alpha_i$ along the canonical bijection $\coprod_{i\in\iota}\alpha_i\cong\alpha$. In particular $r(\sigma_{r,p}(a))=r(a)$ for every $a\in\alpha$: the permutation $\sigma_{r,p}$ maps each fibre onto itself.
--
--   This construction is used to bound numbers of standard fillings from below. For a finite poset $\alpha$, a standard filling is a bijection $\alpha\to\{0,\dots,|\alpha|-1\}$ that is strictly increasing. If $r$ is a strictly monotone rank function from $\alpha$ to a finite linearly ordered set (for instance the anti-diagonal index $i+j$ on the cells of a Young diagram), then composing one enumeration of $\alpha$ that is compatible with the ranks with the fibrewise permutations $\sigma_{r,p}$ produces pairwise distinct standard fillings, which gives at least $\prod_i|\alpha_i|!$ of them.
--
--   **Formalization Note** `fiberPermutation r p` is the `Equiv.Perm α` obtained by conjugating `Equiv.sigmaCongrRight p` with `Equiv.sigmaFiberEquiv r`; the fibre $\alpha_i$ is the subtype `{a // r a = i}`. No finiteness or order assumptions are made on $\alpha$ or $\iota$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/RankFillings.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/RankFillings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def fiberPermutation {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a = i}) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv r).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv r))

end
end Tableau
end PartialPermutation
end

end OAI


