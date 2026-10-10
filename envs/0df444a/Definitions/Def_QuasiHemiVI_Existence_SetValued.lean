-- Prove2me | Definitions.Def_QuasiHemiVI_Existence_SetValued
-- name    : QuasiHemiVI_Existence_SetValued
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:26.825658+00:00
-- url     : https://prove2.me/theorems/b275aee6-66a5-46ea-a57d-ca5ec5d22a13
-- title:
--   Upper semicontinuous multivalued maps (Definition 2.1 (i)) and sequentially weakly closed graphs
-- statement:
--   Let $\alpha,\beta$ be topological spaces, $F:\alpha\to2^\beta$ a multivalued map and $s\subseteq\alpha$.
--
--   1. $F$ is **upper semicontinuous on $s$** if for every $x\in s$ and every open set $O\subseteq\beta$ with $F(x)\subseteq O$ there is a neighbourhood $N$ of $x$ in $s$ (for the subspace topology) such that $F(y)\subseteq O$ for all $y\in N$. This is Definition 2.1 (i) for the restriction $F|_s:s\to2^\beta$.
--   2. For a real normed space $E$, a set $C\subseteq E$ and a multivalued map $\Psi:C\to2^C$, the **graph of $\Psi$ is sequentially weakly closed** if, whenever $w_n\in C$, $u_n\in\Psi(w_n)$, $w_n\rightharpoonup w$ and $u_n\rightharpoonup u$ with $w,u\in C$, one has $u\in\Psi(w)$.
--
--   The first notion is hypothesis (HT)(i) on the operator $T:C\to2^{V^*}$; the second is the graph condition of Kluge's fixed point theorem (Theorem 2.7) and of the variational selection in the proof of Theorem 3.8.
--
--   **Formalization Note** Multivalued maps are total functions `α → Set β`; only their values on `s` (resp. `C`) enter the two predicates.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1248, Definition 2.1 (i); p. 1249, Theorem 2.7 (graph sequentially weakly closed)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv

namespace QuasiHemiVI.Existence

open Filter Topology

/-- Upper semicontinuity of a multivalued map on a subset (Definition 2.1 (i), p. 1248): the
restriction of `F : α → Set β` to `s` (with the subspace topology) is upper semicontinuous, i.e.
for every `x ∈ s` and every open `O ⊆ β` with `F x ⊆ O` there is a neighbourhood `N` of `x`
in `s` with `F y ⊆ O` for all `y ∈ N`. -/
def IsUSCOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (F : α → Set β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ O : Set β, IsOpen O → F x ⊆ O → ∀ᶠ y in 𝓝[s] x, F y ⊆ O

/-- The graph of a multivalued map `Ψ : C → 2^C` is sequentially weakly closed (in `C × C`):
whenever `w n ∈ C`, `u n ∈ Ψ (w n)`, `w n ⇀ w₀` and `u n ⇀ u₀` with `w₀, u₀ ∈ C`, then
`u₀ ∈ Ψ w₀`. -/
def SeqWeaklyClosedGraphOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (Ψ : E → Set E) : Prop :=
  ∀ (w u : ℕ → E) (w₀ u₀ : E), (∀ n, w n ∈ C) → (∀ n, u n ∈ Ψ (w n)) → w₀ ∈ C → u₀ ∈ C →
    WeakConv w w₀ → WeakConv u u₀ → u₀ ∈ Ψ w₀

end QuasiHemiVI.Existence


