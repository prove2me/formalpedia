-- Prove2me | Definitions.Def_CostlySeeding_EdgeQuery_SetFunction
-- name    : CostlySeeding_EdgeQuery_SetFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:00.35945+00:00
-- url     : https://prove2.me/theorems/8faa0871-5180-4895-9984-3dc5dc29c04d
-- title:
--   Finite set-function maximum, monotonicity, and submodularity
-- statement:
--   For a real-valued function $f$ on the subsets of an $n$-element vertex set, define its size-$k$ optimum by
--
--   $$
--   \operatorname{OPT}_k(f)=\max_{S\subseteq V,\ |S|=k} f(S).
--   $$
--
--   The module also records the standard monotonicity condition $S\subseteq T\Rightarrow f(S)\le f(T)$ and submodularity condition $f(S\cup T)+f(S\cap T)\le f(S)+f(T)$. These general set-function notions are used by the paper's cascade optimum, approximation-transfer lemma, and sketch guarantee.
--
--   **Formalization Note** If $k>n$, the feasible family is empty and the auxiliary optimum returns zero. Every theorem using that optimum assumes or witnesses a feasible size.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 8, Definition 1 and monotone-submodular discussion; p. 15, Lemma 1; p. 17, §3.3

import Mathlib

namespace CostlySeeding.EdgeQuery

noncomputable def OPTof {n : ℕ} (f : Finset (Fin n) → ℝ) (k : ℕ) : ℝ :=
  if h : ((Finset.univ : Finset (Fin n)).powersetCard k).Nonempty then
    ((Finset.univ : Finset (Fin n)).powersetCard k).sup' h f
  else 0

def MonotoneSet {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T, S ⊆ T → f S ≤ f T

def SubmodularSet {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

end CostlySeeding.EdgeQuery


