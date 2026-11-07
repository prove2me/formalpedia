-- Prove2me | Definitions.Def_GenSort_removalSet
-- name    : GenSort_removalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:06.728687+00:00
-- url     : https://prove2.me/theorems/80d9043f-22f4-4371-91f8-6db872e2f23d
-- title:
--   Candidate removal set $C_\tau$
-- statement:
--   A left vertex $u$ is **marked** if a queried edge $(u, S_i)$ at a sampled right vertex is incorrectly oriented ($S_i \prec_\pi u$). The **candidate removal set** is
--   $$
--   C_\tau = \bigcup_{\text{marked } u \in L} E_H[u, \Gamma(u)] \;\cup\; \bigcup_{v \in R} Q_v ,
--   $$
--   all edges at marked left vertices together with, at every right vertex $v$, the edges to its selected highest-score neighbours $Q_v$ (computed from the scores under $\tau$).
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 steps 2 and 5, pp.7–8 (PDF pp.9–10)

import Mathlib

namespace GenSort

/-- **The candidate removal set `C_τ`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 steps 2 and 5, p.7–8 (PDF pp.9–10):
`C_τ = ⋃_{marked u ∈ L} E_H[u, Γ(u)] ∪ ⋃_{v ∈ R} Q_v`. A left vertex `u` is marked if some
queried edge `(u, S_i)` at a sampled right vertex is incorrectly oriented (`S_i ≺_π u`). `Q`
is the selection of step 4 (computed from the scores under `τ`).

**Formalization Note.** `C_τ` is a subset of the current edge set `E`; an edge `(u, v)` belongs
to it iff `u` is marked or `u ∈ Q v`. -/
noncomputable def removalSet {n : ℕ} {L R : Type*} {s : ℕ} (E : Finset (L × R)) (ℓ : L → Fin n)
    (r : R → Fin n) (π : Equiv.Perm (Fin n)) (S : Fin s → R) (Q : R → Finset L) :
    Finset (L × R) :=
  open Classical in
  E.filter fun p =>
    (∃ i, (p.1, S i) ∈ E ∧ π.symm (r (S i)) < π.symm (ℓ p.1)) ∨ p.1 ∈ Q p.2

end GenSort


