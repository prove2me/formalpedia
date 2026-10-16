-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
-- name    : OAI_NumberTheory_ShortEgyptian_SamplePartitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:39:50.581925+00:00
-- url     : https://prove2.me/theorems/e4f73c2a-eb97-4c1c-8a61-18e67a80abc6
-- title:
--   Splitting random samples along disjoint coordinate blocks and along a Boolean selection
-- statement:
--   Let $J$ be a set of coordinates and $A$ a set of values. A sample is a map $J\to A$, and $Y^X$ denotes the set of all maps $X\to Y$.
--
--   1. **Merging.** For finite $J$, subsets $L,R\subseteq J$, and maps $z:J\setminus(L\cup R)\to A$, $x:L\to A$, $y:R\to A$, the merged sample $m(z,x,y):J\to A$ is
--
--      $$m(z,x,y)(j)=\begin{cases}x(j), & j\in L,\\ y(j), & j\in R\setminus L,\\ z(j), & j\notin L\cup R.\end{cases}$$
--
--   2. **Partition of samples.** If $J$ is finite and $L,R\subseteq J$ are disjoint, restriction to the three blocks is a bijection
--
--      $$A^{J}\longrightarrow A^{J\setminus(L\cup R)}\times\bigl(A^{L}\times A^{R}\bigr),\qquad f\longmapsto\bigl(f|_{J\setminus(L\cup R)},\,f|_{L},\,f|_{R}\bigr),$$
--
--      whose inverse is merging.
--
--   3. **Normalization along a selection.** For arbitrary sets $J,A$ and a selection $I:J\to\{0,1\}$, the map
--
--      $$A^{J\times\{0,1\}}\longrightarrow A^{J}\times A^{J},\qquad f\longmapsto\Bigl(j\mapsto f\bigl(j,I(j)\bigr),\ j\mapsto f\bigl(j,1-I(j)\bigr)\Bigr)$$
--
--      is a bijection; its inverse sends $(g,h)$ to the map whose value at $(j,b)$ is $g(j)$ if $b=I(j)$ and $h(j)$ otherwise.
--
--   Because these maps are bijections, uniform averages over samples factor accordingly: an average over $f\in A^{J}$ equals an iterated average over the three restricted blocks, and an average over doubled samples $f\in A^{J\times\{0,1\}}$ equals an iterated average over the part selected by $I$ and the complementary part. This is how, for two selections that differ on every coordinate of $L\cup R$, correlations of products of random primes are reduced to bilinear sums over the fresh primes indexed by $L$ and by $R$.
--
--   **Formalization Note** The Lean names are `mergeSamples`, `partitionSamples` and `normalizeSamples`. The bijections are Lean equivalences (`Equiv`), the block outside L and R is a `Finset` complement, bits are `Bool` with Boolean negation in place of 1 - I(j), and the case distinctions use classical decidability. The private lemma `dite_eq_left` is a technical rewriting rule for dependent if-then-else.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uJ uA uE uM uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def mergeSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J)
    (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) (j : J) : A :=
  if hj : j ∈ L then x ⟨j,hj⟩ else if hjR : j ∈ R then y ⟨j,hjR⟩ else
    z ⟨j,by simp only [mem_compl,mem_union]; tauto⟩

noncomputable def partitionSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J)
    (hdis : Disjoint L R) :
    (J → A) ≃ ((((L∪R)ᶜ : Finset J) → A) × ((L → A) × (R → A))) where
  toFun f := (fun j => f j,(fun j => f j, fun j => f j))
  invFun v := mergeSamples L R v.1 v.2.1 v.2.2
  left_inv f := by funext j; simp only [mergeSamples]; split_ifs <;> rfl
  right_inv v := by
    apply Prod.ext
    · funext j
      have hl : j.val ∉ L := by have hh := mem_compl.mp j.property; exact fun h => hh (mem_union.mpr (Or.inl h))
      have hr : j.val ∉ R := by have hh := mem_compl.mp j.property; exact fun h => hh (mem_union.mpr (Or.inr h))
      simp [mergeSamples,hl,hr]
    · apply Prod.ext
      · funext j; simp only [mergeSamples,j.property,dite_eq_left]
      · funext j
        have hl : j.val ∉ L := fun h => disjoint_left.mp hdis h j.property
        simp [mergeSamples,hl,j.property]

noncomputable def normalizeSamples {J : Type uJ} {A : Type uA} (I : J → Bool) :
    ((J × Bool) → A) ≃ ((J → A) × (J → A)) where
  toFun f := (fun j => f (j,I j),fun j => f (j,!(I j)))
  invFun v jb := if jb.2 = I jb.1 then v.1 jb.1 else v.2 jb.1
  left_inv f := by funext ⟨j,b⟩; cases hj : I j <;> cases b <;> simp [hj]
  right_inv v := by
    apply Prod.ext <;> funext j <;> simp

end ShortEgyptian

end OAI


