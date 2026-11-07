-- Prove2me | Definitions.Def_PlantedSubgraphLD_IsDivisible
-- name    : PlantedSubgraphLD_IsDivisible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:56.907119+00:00
-- url     : https://prove2.me/theorems/976290f0-9888-4ae0-ae61-f53be90db248
-- title:
--   $(\ell,C,a)$-divisibility of a graph
-- statement:
--   Let $\ell,C,a$ be positive integers. A graph $\Gamma$ is **$(\ell,C,a)$-divisible** if every connected graph $F$ with $N_\Gamma(F)>0$ and $e(F)\ge\ell$ has an ordered edge decomposition $\mathcal T(F)=(T_1,\dots,T_m)$ with
--
--   $$
--   \ell\le e(T_i)\le C\ell\quad(i=1,\dots,m),\qquad \mathrm{ov}(F,\mathcal T(F))\le a(m-1).
--   $$
--
--   Divisibility is the only property of the planted graph that the decomposition argument of §4.2 uses; Lemma 4.4 shows that treewidth at most $k$ gives $(\ell,3,k+1)$-divisibility for every $\ell$.
--
--   **Formalization Note** Stated on the concrete copies: for every edge set $S\subseteq E(\Gamma)$ spanning a connected graph with $|S|\ge\ell$. A connected abstract graph with $N_\Gamma(F)>0$ is the class of such an $S$, and decompositions transport along isomorphisms with the same piece sizes and overlap (p.18), so the two forms are equivalent. Positivity of $\ell,C,a$ is assumed where the notion is used.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_ov

open Classical

namespace PlantedSubgraphLD

/-- `(ℓ, C, a)`-divisibility of a graph `Γ`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, pp.19–20: "Let ℓ, C, a be positive
integers. We say that a graph Γ is (ℓ, C, a)-divisible if, for every connected graph F with
NΓ(F) > 0 and e(F) ≥ ℓ, there exists an ordered edge decomposition T(F) = (T1, …, Tm) such that
ℓ ≤ e(Ti) ≤ Cℓ for every i = 1, 2, …, m, ov(F, T(F)) ≤ a(m − 1)."

**Formalization Note** Stated on the concrete copies: for every edge set `S ⊆ E(Γ)` spanning a
connected graph with `|S| ≥ ℓ`. A connected abstract graph `F` with `N_Γ(F) > 0` is the class of
such an `S`, and an ordered edge decomposition of `F` is one of `S` transported along an
isomorphism (p.18), with the same piece sizes and the same overlap count; so the two forms are
equivalent. Positivity of `ℓ, C, a` is assumed where the notion is used. -/
def IsDivisible {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V) (ℓ C a : ℕ) : Prop :=
  ∀ S : Finset (Sym2 V), S ⊆ Γ.edgeFinset → (spanned S).Connected → ℓ ≤ S.card →
    ∃ (m : ℕ) (T : Fin m → Finset (Sym2 V)), IsOrderedEdgeDecomp S T ∧
      (∀ i, ℓ ≤ (T i).card ∧ (T i).card ≤ C * ℓ) ∧ ov S T ≤ (a : ℤ) * ((m : ℤ) - 1)

end PlantedSubgraphLD


