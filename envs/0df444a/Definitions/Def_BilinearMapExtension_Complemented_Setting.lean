-- Prove2me | Definitions.Def_BilinearMapExtension_Complemented_Setting
-- name    : BilinearMapExtension_Complemented_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:13.216612+00:00
-- url     : https://prove2.me/theorems/9e1fe4e5-b6a6-4902-8b03-948205cc41ff
-- title:
--   §2 pp. 1–2, §4 p. 3 — complemented subspaces, projections onto a subspace, extensions of bounded bilinear maps
-- statement:
--   Throughout, $\mathbb F$ is $\mathbb R$ or $\mathbb C$ and all spaces are normed spaces over $\mathbb F$. A **linear manifold** of a normed space $\mathcal X$ is a linear subspace, not necessarily closed; a **subspace** is a closed linear manifold. For a linear manifold $\mathcal M$, $\mathcal M^-$ denotes its closure.
--
--   This item fixes three notions.
--
--   1. **Complemented subspace.** A subspace $\mathcal S$ of $\mathcal X$ is *complemented* if it has a subspace as an algebraic complement: $\mathcal S$ is closed and there is a closed linear manifold $\mathcal T$ with
--   $$\mathcal S \cap \mathcal T = \{0\}, \qquad \mathcal S + \mathcal T = \mathcal X.$$
--   2. **Projection onto a subspace.** A bounded linear operator $E \in \mathcal B[\mathcal X,\mathcal X]$ is a projection with range $\mathcal R(E) = \mathcal S$ if $E$ maps $\mathcal X$ into $\mathcal S$ and acts as the identity on $\mathcal S$; equivalently $E^2 = E$ and $\mathcal R(E) = \mathcal S$.
--   3. **Extension of a bilinear map.** Let $\mathcal M \subseteq \mathcal X$ and $\mathcal N \subseteq \mathcal Y$ be linear manifolds and $\phi \in \boldsymbol b[\mathcal M\times\mathcal N,\mathcal Z]$ a bounded bilinear map. A bounded bilinear map $\widehat\phi \in \boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]$ *extends* $\phi$, written $\widehat\phi|_{\mathcal M\times\mathcal N} = \phi$, if $\widehat\phi(u,v) = \phi(u,v)$ for every $(u,v) \in \mathcal M\times\mathcal N$.
--
--   These are the objects of Kubrusly's extension theorem (Theorem 5.2): bounded bilinear maps on $\mathcal M\times\mathcal N$ extend to $\mathcal X\times\mathcal Y$ for every Banach target exactly when $\mathcal M^-$ and $\mathcal N^-$ are complemented.
--
--   **Formalization Note.** A linear manifold is a `Submodule 𝕜 X` over `[RCLike 𝕜]`; its closure is `M.topologicalClosure`. "Complemented" requires the complement to be *closed*: a bare algebraic complement exists for every subspace and would make the notion empty. A bounded bilinear map $\mathcal M\times\mathcal N\to\mathcal Z$ is encoded as a continuous linear map `M →L[𝕜] N →L[𝕜] Z` (curried), with Mathlib's operator norm; Proposition 4.2 of the paper ($\boldsymbol b[\mathcal X\times\mathcal Y,\mathcal Z]\cong\mathcal B[\mathcal X,\mathcal B[\mathcal Y,\mathcal Z]]$ isometrically) is what makes this encoding faithful, and it is stated as a separate item.
-- source:
--   Kubrusly, On extensions of bilinear maps, arXiv:2110.03102v2, pp. 1–3, §2 (subspaces, closures, bounded bilinear maps) and §4 (complemented subspaces, p. 3)

import Mathlib

namespace BilinearMapExtension.Complemented

/-- §4, p. 3: a subspace (= closed linear manifold, §2 p. 1) `S` of a normed space `X` is
*complemented* if it has a subspace (a closed linear manifold) as an algebraic complement. -/
def IsComplementedSubspace {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (S : Submodule 𝕜 X) : Prop :=
  IsClosed (S : Set X) ∧ ∃ T : Submodule 𝕜 X, IsClosed (T : Set X) ∧ IsCompl S T

/-- A (bounded) projection `E ∈ B[X, X]` with range `R(E) = S`: `E` maps `X` into `S` and acts
as the identity on `S` (equivalently, `E ∘ E = E` and `R(E) = S`). -/
def IsProjectionOnto {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (E : X →L[𝕜] X) (S : Submodule 𝕜 X) : Prop :=
  (∀ x, E x ∈ S) ∧ ∀ x ∈ S, E x = x

/-- `φh ∈ b[X×Y, Z]` extends `φ ∈ b[M×N, Z]` (notation `φh|M×N = φ`): the two agree on every
pair `(u, v) ∈ M×N`. Bounded bilinear maps are encoded as continuous linear maps into continuous
linear maps (`b[X×Y, Z] ≅ B[X, B[Y, Z]]`, Proposition 4.2). -/
def IsBilinExtension {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (φ : M →L[𝕜] N →L[𝕜] Z) (φh : X →L[𝕜] Y →L[𝕜] Z) : Prop :=
  ∀ (u : M) (v : N), φh u v = φ u v

end BilinearMapExtension.Complemented


