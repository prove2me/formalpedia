-- Prove2me | Definitions.Def_HScattered_LinearSets_Equivalence
-- name    : HScattered_LinearSets_Equivalence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:06.671417+00:00
-- url     : https://prove2.me/theorems/540586d0-f4ef-46f9-b2b9-0fa17913dc00
-- title:
--   ΓL(r, qⁿ)-equivalence of subspaces and PΓL(r, qⁿ)-equivalence of linear sets
-- statement:
--   Let $V$ be a vector space over $\mathbb F_{q^n}$. An element of $\Gamma\mathrm L(V)$ ($=\Gamma\mathrm L(r,q^n)$ when $\dim V = r$) is a bijective additive map $f\colon V\to V$ for which there is a field automorphism $\sigma$ of $\mathbb F_{q^n}$ with
--
--   $$
--   f(a v) = a^{\sigma} f(v) \qquad\text{for all } a\in\mathbb F_{q^n},\ v\in V .
--   $$
--
--   Such an $f$ induces the collineation $\varphi_f$ of $\mathrm{PG}(V,\mathbb F_{q^n})$, which maps a subspace $P$ to $\langle f(P)\rangle_{\mathbb F_{q^n}}$; in particular $\varphi_f(\langle u\rangle_{\mathbb F_{q^n}}) = \langle f(u)\rangle_{\mathbb F_{q^n}}$. The group $\mathrm{P}\Gamma\mathrm L(r,q^n)$ consists of these induced collineations.
--
--   1. Two linear sets $L_U$ and $L_W$ are **$\mathrm P\Gamma\mathrm L$-equivalent** if $L_U^{\varphi} = L_W$ for some $\varphi \in \mathrm P\Gamma\mathrm L(r,q^n)$, i.e. if $\varphi_f(L_U) = L_W$ for some $f\in\Gamma\mathrm L(r,q^n)$.
--   2. Two $\mathbb F_q$-subspaces $U$ and $W$ are **$\Gamma\mathrm L$-equivalent** (lie in the same $\Gamma\mathrm L(r,q^n)$-orbit) if $U^f = W$ for some $f\in\Gamma\mathrm L(r,q^n)$.
--
--   Since $L_{U^f} = L_U^{\varphi_f}$, the second relation implies the first; Theorem 4.5 is about the converse.
--
--   **Formalization Note** $\Gamma\mathrm L$ is encoded by `IsSemilinearAut K f` for `f : V ≃+ V`: there is `σ : K ≃+* K` with `f (a • v) = σ a • f v`. The automorphism $\sigma$ is arbitrary, so linear maps ($\mathrm{GL}$) are a special case and not the whole group. The induced collineation is `collineation K f P = span K (f '' P)`, and $\mathrm{P}\Gamma\mathrm L$-equivalence quantifies over $f \in \Gamma\mathrm L$, which is exactly the set of elements of $\mathrm P\Gamma\mathrm L$. The image $U^f$ is the set image `f '' U`.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 12, §4 (PΓL-equivalence, L_{U^f} = L_U^{φ_f}, ΓL-orbits)

import Mathlib
import Definitions.Def_HScattered_LinearSets_LinearSet

namespace HScattered.LinearSets

/-- An element of `ΓL(V)` (`ΓL(r, qⁿ)` for `V = V(r, qⁿ)`): an additive bijection `f` of `V`
that is semilinear over `K` with respect to some field automorphism `σ` of `K`,
`f (a • v) = σ a • f v`. -/
def IsSemilinearAut (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V ≃+ V) : Prop :=
  ∃ σ : K ≃+* K, ∀ (a : K) (v : V), f (a • v) = σ a • f v

/-- The collineation `φ_f` of `PG(V, K)` induced by `f ∈ ΓL(V)`: it sends the subspace `P`
(in particular a point `⟨u⟩_K`) to the `K`-span of its image `f(P)`. For semilinear `f`,
`φ_f ⟨u⟩_K = ⟨f u⟩_K`. -/
def collineation (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V ≃+ V) (P : Submodule K V) : Submodule K V :=
  Submodule.span K (f '' (P : Set V))

/-- §4, p. 12. Two linear sets `L_U`, `L_W` are `PΓL`-equivalent if some element of
`PΓL(r, qⁿ)` maps `L_U` onto `L_W`; every element of `PΓL(r, qⁿ)` is the collineation `φ_f`
induced by some `f ∈ ΓL(r, qⁿ)`. -/
def PGammaLEquivalent (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U W : Submodule F V) : Prop :=
  ∃ f : V ≃+ V, IsSemilinearAut K f ∧
    collineation K f '' linearSet F K U = linearSet F K W

/-- §4, p. 12. The `𝔽_q`-subspaces `U` and `W` are `ΓL(r, qⁿ)`-equivalent (lie in the same
`ΓL(r, qⁿ)`-orbit) if `U^f = W` for some `f ∈ ΓL(r, qⁿ)`. -/
def GammaLEquivalent (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U W : Submodule F V) : Prop :=
  ∃ f : V ≃+ V, IsSemilinearAut K f ∧ f '' (U : Set V) = (W : Set V)

end HScattered.LinearSets


