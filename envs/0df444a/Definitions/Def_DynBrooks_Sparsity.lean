-- Prove2me | Definitions.Def_DynBrooks_Sparsity
-- name    : DynBrooks_Sparsity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:03.815058+00:00
-- url     : https://prove2.me/theorems/ca7e0f4f-fbcc-40bd-9414-84774017e528
-- title:
--   §4.1.1 — the sparsity $\zeta_F(v)$
-- statement:
--   Let $F$ be a graph of maximum degree at most $\Delta$. The **sparsity** of a vertex $v$ is
--
--   $$\zeta_F(v)=\frac1\Delta\left(\binom\Delta2-\bigl|E(F[N_F(v)])\bigr|\right),$$
--
--   where $|E(F[N_F(v)])|$ is the number of edges of $F$ with both endpoints in the neighborhood of $v$. Sparsity is measured relative to the fixed degree bound $\Delta$, so both missing edges among the neighbors of $v$ and degree deficiency contribute.
--
--   **Formalization Note** $\zeta$ is real-valued. At $\Delta=0$ the factor $1/\Delta$ is $0$ in Lean; no statement uses that case.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §4.1.1, p.15 (PDF 17)

import Mathlib

namespace DynBrooks

/-! # Sparsity

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §4.1.1,
p.15 (PDF 17): `ζ_F(v) = (1/∆) ( (∆ 2) − |E(F[N_F(v)])| )`. Sparsity is measured relative to the fixed
degree bound `∆`, so degree deficiency and missing edges among the neighbors both contribute.

**Formalization Note.** `ζ` takes real values. `Δ = 0` gives `1/0 = 0`, and no statement of the mission
uses that case. -/

open Classical in
/-- `|E(F[N_F(v)])|`: the number of edges of `F` with both endpoints neighbors of `v`. -/
noncomputable def nbrEdges {V : Type} [Fintype V] (F : SimpleGraph V) (v : V) : ℕ :=
  (F.edgeFinset.filter fun e => ∀ x ∈ e, F.Adj v x).card

/-- The sparsity `ζ_F(v)` relative to the degree bound `Δ`. -/
noncomputable def sparsity {V : Type} [Fintype V] (Δ : ℕ) (F : SimpleGraph V) (v : V) : ℝ :=
  (1 / (Δ : ℝ)) * ((Δ.choose 2 : ℝ) - (nbrEdges F v : ℝ))

end DynBrooks


