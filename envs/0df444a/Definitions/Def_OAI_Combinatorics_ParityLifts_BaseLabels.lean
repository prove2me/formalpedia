-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
-- name    : OAI_Combinatorics_ParityLifts_BaseLabels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:06:18.551641+00:00
-- url     : https://prove2.me/theorems/5eb628c0-8a4e-45eb-b903-b158d8478e3b
-- title:
--   Partial label readouts on the base graph of a choice system
-- statement:
--   Let $C$ be a choice system on $t$ indices: finite domains $D_i$ for $i\in[t]=\{0,\dots,t-1\}$ and, for every pair $p=(i,j)$ with $i<j$, a finite label set $L_p$ with label maps $\lambda^{\mathrm L}_p\colon D_i\to L_p$ and $\lambda^{\mathrm R}_p\colon D_j\to L_p$. Its base graph $G_C$ has main vertices $(i,d)$ with $d\in D_i$, and helper vertices $(h,q)$, where $h=h_{ij;\ell}$ is a helper of the template (a pair $i<j$ together with a third index $\ell\notin\{i,j\}$) and $q\in L_{ij}$. This file defines partial functions on base vertices that return a label when the vertex has the relevant type and are undefined (value $\bot$) otherwise.
--
--   1. **Left label at a pair $p=(i,j)$.**
--   $$
--   \mathrm{left}_p(v)=\begin{cases}\lambda^{\mathrm L}_p(d)&\text{if } v=(i,d) \text{ for some } d\in D_i,\\ \bot&\text{otherwise.}\end{cases}
--   $$
--   2. **Right label at $p=(i,j)$.** $\mathrm{right}_p(v)=\lambda^{\mathrm R}_p(e)$ if $v=(j,e)$ with $e\in D_j$, and $\mathrm{right}_p(v)=\bot$ otherwise.
--   3. **Helper label at a helper $h$.** $\mathrm{helper}_h(v)=q$ if $v=(h,q)$ is a helper vertex of exactly the type $h$, and $\mathrm{helper}_h(v)=\bot$ otherwise.
--
--   Three evaluation rules record the defining cases: $\mathrm{left}_p(i,d)=\lambda^{\mathrm L}_p(d)$, $\mathrm{right}_p(j,e)=\lambda^{\mathrm R}_p(e)$ and $\mathrm{helper}_h(h,q)=q$.
--
--   These readouts let label conditions be stated uniformly for an arbitrary base vertex, such as the image $\varphi(x)$ of a source vertex under a homomorphism $\varphi\colon F\to G_C$, whose type is not fixed in advance. They are used to express that edges of the base graph force agreement of labels, and to define the label-mismatch tests of the choice-extraction argument.
--
--   **Formalization Note** The undefined value is `none` in an `Option` type. The definitions are `leftLabelAt`, `rightLabelAt` and `helperLabelAt`, and the evaluation rules are the simp lemmas `leftLabelAt_self`, `rightLabelAt_self` and `helperLabelAt_self`. In the defining case the domain element is transported along the equality of indices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses

namespace OAI

namespace ParityWL

open scoped BigOperators

section BaseLabels

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t)

noncomputable def leftLabelAt (p : MainPair t) : BaseVertex C → Option (C.Label p)
  | .inl ⟨i, d⟩ => if h : i = p.1.1 then some (C.leftLabel p (h ▸ d)) else none
  | .inr _ => none

noncomputable def rightLabelAt (p : MainPair t) : BaseVertex C → Option (C.Label p)
  | .inl ⟨i, d⟩ => if h : i = p.1.2 then some (C.rightLabel p (h ▸ d)) else none
  | .inr _ => none

noncomputable def helperLabelAt (h : Helper t) : BaseVertex C → Option (C.Label h.1.1)
  | .inl _ => none
  | .inr ⟨j, q⟩ => if he : j = h then some (he ▸ q) else none

@[simp] lemma leftLabelAt_self (p : MainPair t) (d : C.Domain p.1.1) :
    leftLabelAt C p (.inl ⟨p.1.1, d⟩) = some (C.leftLabel p d) := by
  simp [leftLabelAt]

@[simp] lemma rightLabelAt_self (p : MainPair t) (d : C.Domain p.1.2) :
    rightLabelAt C p (.inl ⟨p.1.2, d⟩) = some (C.rightLabel p d) := by
  simp [rightLabelAt]

@[simp] lemma helperLabelAt_self (h : Helper t) (q : C.Label h.1.1) :
    helperLabelAt C h (.inr ⟨h, q⟩) = some q := by
  simp [helperLabelAt]

end BaseLabels

end ParityWL

end OAI


