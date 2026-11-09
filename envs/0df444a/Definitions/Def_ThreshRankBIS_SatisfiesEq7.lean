-- Prove2me | Definitions.Def_ThreshRankBIS_SatisfiesEq7
-- name    : ThreshRankBIS_SatisfiesEq7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:04:31.50673+00:00
-- url     : https://prove2.me/theorems/a3c99eac-4663-4e8d-90a0-6e8a1c73d62c
-- title:
--   Lists of approximate cuts: Lemma 6's success property and display (7)
-- statement:
--   Fix $0<\rho<1$ and let $U$ be the spectral subspace of $L_G$ for the eigenvalues at most $\rho d$. A family $\mathcal C$ of vertex sets has **Lemma 6's success property** if every $S\subseteq V(G)$ has a representative $C\in\mathcal C$ with
--
--   $$
--   |S\triangle C|\le 16\bigl(\mathrm{dist}(\mathbf 1_S,U)^2+1\bigr).
--   $$
--
--   With $\kappa=\lceil 256/\rho\rceil$, the family **satisfies (7)** if every closed $A\subseteq X$ has some $C\in\mathcal C$ with
--
--   $$
--   |S_A\triangle C|\le\kappa\,(t(A)+1).
--   $$
--
--   Section 4 of the paper fixes a list of approximate cuts satisfying (7), $K=|\mathcal C|$, and every container bound (Lemma 10, display (16), Corollary 12) takes such a list as its hypothesis.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 6, p.9; display (7), p.10; §4, p.12

import Mathlib
import Definitions.Def_ThreshRankBIS_closure
import Definitions.Def_ThreshRankBIS_thresholdRank
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- The constant `κ = ⌈256/ρ⌉` (p.10). -/
noncomputable def kappa (ρ : ℝ) : ℕ := ⌈256 / ρ⌉₊

/-- The success property of the list of approximate cuts of **Lemma 6** (p.9): every
`S ⊆ V(G)` has a representative `C ∈ 𝒞` with `|S △ C| ≤ 16 (dist(1_S, U)² + 1)`, where `U` is the
spectral subspace of `L_G` for the eigenvalues at most `ρd`. -/
def SpectralCover {n : ℕ} (ρ : ℝ) (E : Fin n → Fin n → Bool) (d : ℕ)
    (𝒞 : Finset (Finset (V n))) : Prop :=
  ∀ S : Finset (V n), ∃ C ∈ 𝒞, (#(symmDiff S C) : ℝ) ≤ 16 * (distU2 ρ E d S + 1)

/-- **Display (7)** (p.10): a family `𝒞` of vertex sets such that every closed `A ⊆ X` has some
`C ∈ 𝒞` with `|S_A △ C| ≤ κ(t(A) + 1)`, `κ = ⌈256/ρ⌉`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), p.10, display (7);
Lemma 6, p.9.

Section 4 (p.12) fixes "a list of approximate cuts satisfying (7)", and Lemma 10, display (16)
and Corollary 12 take such a family as their hypothesis, with `K = |𝒞|`. The module also defines
`κ` and the success property of Lemma 6 (`SpectralCover`). -/
def SatisfiesEq7 {n : ℕ} (ρ : ℝ) (E : Fin n → Fin n → Bool) (𝒞 : Finset (Finset (V n))) :
    Prop :=
  ∀ A : Finset (Fin n), IsClosedLeft E A →
    ∃ C ∈ 𝒞, (#(symmDiff (SA E A) C) : ℝ) ≤ (kappa ρ : ℝ) * ((deficit E A : ℝ) + 1)

end ThreshRankBIS


