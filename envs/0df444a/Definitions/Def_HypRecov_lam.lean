-- Prove2me | Definitions.Def_HypRecov_lam
-- name    : HypRecov_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:26.92634+00:00
-- url     : https://prove2.me/theorems/3b11af4a-e114-4b92-aeec-d609c7e85d94
-- title:
--   Local edge connectivity $\lambda_H(u,v)$
-- statement:
--   For vertices $u\ne v$, $\lambda_H(u,v)$ is the minimum of $\mathrm{cut}_H(S)$ over the sets $S$ containing exactly one of $u,v$; the same for a weighted hypergraph $\widehat H$ with $\mathrm{cut}_{\widehat H}$.
--
--   **Formalization Note** It is the infimum in $\mathbb N$ of the cut values; for $u=v$ there is no such $S$ and the value is $0$, which no statement uses.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 7.2, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_cutW

namespace HypRecov

/-- **Local edge connectivity `λ_H(u, v)`.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 7.2, p.19 (PDF p.20):
"λ_H(u, v) is the minimum capacity of a cut separating u and v."

**Formalization Note.** The infimum in `ℕ` over the cuts `S` containing exactly one of `u, v`. For
`u ≠ v` the set is nonempty, so this is a minimum; for `u = v` it is empty and the value is `0`,
which no statement uses. -/
noncomputable def lam {n : ℕ} (E : Finset (Finset (Fin n))) (u v : Fin n) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset (Fin n), (u ∈ S ↔ v ∉ S) ∧ cut E S = c}

/-- The same for a weighted hypergraph `Ĥ`: `λ_Ĥ(u, v)`, the least weighted cut separating `u, v`. -/
noncomputable def lamW {n : ℕ} (H : List (Finset (Fin n) × ℕ)) (u v : Fin n) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset (Fin n), (u ∈ S ↔ v ∉ S) ∧ cutW H S = c}

end HypRecov


