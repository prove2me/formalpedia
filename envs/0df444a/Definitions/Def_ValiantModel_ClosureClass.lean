-- Prove2me | Definitions.Def_ValiantModel_ClosureClass
-- name    : ValiantModel_ClosureClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:14.161772+00:00
-- url     : https://prove2.me/theorems/cc90de1f-c7cb-472b-99a2-475497a881e5
-- title:
--   Definition 14, p.25 — the $k$-query closure class $\mathrm{Cl}_k(H_d)$
-- statement:
--   For $d,k\in\mathbb N$, the **$k$-query closure class** of $H_d$ is
--
--   $$
--   \mathrm{Cl}_k(H_d)=\Bigl\{\bigcap_{h\in V(q,r)}\mathrm{supp}(h)\;:\;q,r\text{ have the same length }t\le k\text{ and }V(q,r)\neq\emptyset\Bigr\}.
--   $$
--
--   It collects the sets a learner can output after a transcript of length at most $k$, and it is the class over which uniform convergence is applied in Theorem 4.9.
--
--   **Formalization Note** A set is represented by its indicator, so the class is a set of hypotheses, in the form the VC dimension and `Set.ncard` take.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.25 (PDF p.27), Definition 14

import Mathlib
import Definitions.Def_ValiantModel_VersionSpaces

namespace ValiantModel

/-- **Definition 14 (k-Query Closure Class)**, arXiv:2605.13840 (version held), p.25 (PDF p.27):
`Cl_k(Hd) = {⋂_{h ∈ V(q, r)} supp(h) : q, r have the same length t ≤ k and V(q, r) ≠ ∅}`.

**Formalization Note.** A subset of the domain is represented by its indicator, so the class is a
set of `Hypothesis d`, as `vcDim` and `Set.ncard` take it. -/
def ClosureClass {d : ℕ} (Hd : Set (Hypothesis d)) (k : ℕ) : Set (Hypothesis d) :=
  {g | ∃ T : List (Point d × Bool), T.length ≤ k ∧ (transcriptVS Hd T).Nonempty ∧
    g = closureOf (transcriptVS Hd T)}

end ValiantModel


