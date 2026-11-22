-- Prove2me | Definitions.Def_TopologicalTensorProduct_Completion
-- name    : TopologicalTensorProduct_Completion
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:21:23.004306+00:00
-- url     : https://prove2.me/theorems/6f42e5a0-c701-45b6-8707-e61d9920255f
-- title:
--   Completions of locally convex spaces and the completed tensor products $E\widehat\otimes_\pi F$, $E\widehat\otimes_\varepsilon F$, $E\overline\otimes F$
-- statement:
--   This file defines what it means for a space to be **a completion** of a locally convex space, and specialises it to the three **completed topological tensor products** of Appendix C.
--
--   All vector spaces are over $\mathbb C$.
--
--   1. Let $X$ be a vector space with a topology $t$. A pair $(Y,i)$, where $Y$ is a topological vector space and $i:X\to Y$ is a linear map, is a **completion** of $(X,t)$ if
--      - $Y$ is a complete Hausdorff locally convex space,
--      - $i$ is injective and $t$ is the topology induced by $i$ from $Y$ (that is, $i$ is a linear topological embedding), and
--      - $i(X)$ is dense in $Y$.
--   2. For topological vector spaces $E,F$, a pair $(Y,i)$ with $i:E\otimes F\to Y$ linear is a **completed projective tensor product** $E\widehat\otimes_\pi F$, a **completed injective tensor product** $E\widehat\otimes_\varepsilon F$, or a **completed inductive tensor product** $E\,\overline\otimes\,F$, if it is a completion of $E\otimes F$ for the projective topology $\pi$, the injective topology $\varepsilon$, or the inductive topology $\iota$, respectively.
--
--   A Hausdorff locally convex space has a completion, and any two completions $(Y,i)$, $(Y',i')$ are related by a unique linear homeomorphism $Y\to Y'$ carrying $i$ to $i'$. Hence a statement about "the" completed tensor product is a statement about every pair $(Y,i)$ satisfying the predicate. This is the form in which kernel theorems are used: e.g. "$\mathcal S(\mathbb R^n)\widehat\otimes_\pi\mathcal S(\mathbb R^m)\simeq\mathcal S(\mathbb R^{n+m})$" says that $\mathcal S(\mathbb R^{n+m})$ with the map $f\otimes g\mapsto f(x)g(y)$ is a completed projective tensor product.
--
--   **Formalization Note.** `MasulloGRH.IsTVSCompletion t i` is the conjunction `IsHLCS Y ∧ IsCompleteTVS Y ∧ Function.Injective i ∧ t = TopologicalSpace.induced i _ ∧ DenseRange i`, with `IsHLCS`, `IsCompleteTVS` (every Cauchy filter converges) and the topologies `projTensorTopology`, `epsTensorTopology`, `indTensorTopology` taken from the platform definition `Def_MasulloGRH_LocallyConvex`. `IsCompletedProjTensor E F i`, `IsCompletedEpsTensor E F i`, `IsCompletedIndTensor E F i` are the three specialisations. The completion is characterised by a predicate instead of being constructed as a type; the paper's notation $E\widehat\otimes_\pi F$ denotes any such $Y$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 675–676, 679 and 682, §C.2.3 (the completions $E\widehat\otimes_\varepsilon F$ after (C.2.3.4), $E\widehat\otimes_\pi F$ after (C.2.3.15), and $E\overline\otimes F$ in (C.2.3.23))

import Definitions.Def_MasulloGRH_LocallyConvex

/-!
# Completions of locally convex spaces and completed topological tensor products

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C, §C.2.3
(pp. 675–676, 679, 682): the completions `E ⊗̂_ε F`, `E ⊗̂_π F` and `E ⊗̄ F` of the injective,
projective and inductive tensor products `E ⊗_ε F`, `E ⊗_π F`, `E ⊗_ι F` of two Hausdorff locally
convex spaces.

A completion is described by its characteristic property: a complete Hausdorff locally convex
space `Y` together with a linear topological embedding `i : X → Y` with dense range.  Any two
completions of `X` are isomorphic by a unique linear homeomorphism compatible with the embeddings,
so a statement about "the" completed tensor product is a statement about every pair `(Y, i)`
satisfying the predicates below.
-/

namespace MasulloGRH

open TensorProduct Topology

universe u v

/-- `(Y, i)` is a *completion* of the vector space `X` endowed with the topology `t`:
`Y` is a complete Hausdorff locally convex space and `i : X → Y` is an injective linear map with
dense range such that `t` is the topology induced by `i` (i.e. `i` is a linear topological
embedding with dense range). -/
def IsTVSCompletion {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →ₗ[ℂ] Y) : Prop :=
  IsHLCS Y ∧ IsCompleteTVS Y ∧ Function.Injective i ∧
    t = TopologicalSpace.induced i ‹TopologicalSpace Y› ∧ DenseRange i

section tensor

variable (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- `(Y, i)` is a completed projective tensor product `E ⊗̂_π F`: a completion of `E ⊗_π F`. -/
def IsCompletedProjTensor (i : E ⊗[ℂ] F →ₗ[ℂ] Y) : Prop :=
  IsTVSCompletion (projTensorTopology E F) i

/-- `(Y, i)` is a completed injective tensor product `E ⊗̂_ε F`: a completion of `E ⊗_ε F`. -/
def IsCompletedEpsTensor (i : E ⊗[ℂ] F →ₗ[ℂ] Y) : Prop :=
  IsTVSCompletion (epsTensorTopology E F) i

/-- `(Y, i)` is a completed inductive tensor product `E ⊗̄ F`: a completion of `E ⊗_ι F`. -/
def IsCompletedIndTensor (i : E ⊗[ℂ] F →ₗ[ℂ] Y) : Prop :=
  IsTVSCompletion (indTensorTopology E F) i

end tensor

end MasulloGRH


