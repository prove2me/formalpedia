-- Prove2me | Definitions.Def_MusicStreaming_Axioms_Supplement_AssociatedClaims
-- name    : MusicStreaming_Axioms_Supplement_AssociatedClaims
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:26:17.669321+00:00
-- url     : https://prove2.me/theorems/1bdb9202-5c45-45dd-bc32-61f7da621907
-- title:
--   §5, p. 15 — the claims problem (N, K, c, E) associated with a streaming problem (N, M, t)
-- statement:
--   With each streaming problem $(N,M,t)$, where $N$ is the set of artists, $M$ the set of users and $t_{ij}$ the number of streams of artist $i$ by user $j$, associate the claims problem
--
--   $$\big(N,\;K(N,M,t),\;c(N,M,t),\;E(N,M,t)\big)\quad\text{with}\quad K=M,\quad c_{ij}=t_{ij},\quad E=m=|M| .$$
--
--   The issues are the users, the characteristic of an artist on an issue is the number of times that user streamed the artist, and the amount to divide is the revenue $m$ (each user pays $1$). The issue totals are $C^j=T^j=\sum_{i\in N}t_{ij}$. Every artist is an agent, including artists nobody streamed.
--
--   **Formalization Note** The streaming problem is the published `MusicStreaming.Axioms.Problem`: artists are `Fin n`, users are natural numbers, and the user set $M$ is the support of the finitely supported stream table, i.e. the users with a nonzero column. The streams are cast to real numbers.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 15, §5 (associated claims problem)

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting
import Definitions.Def_MusicStreaming_Axioms_Supplement_Claims

namespace MusicStreaming.Axioms.Supplement

open MusicStreaming.Axioms

/-- The claims problem associated with a streaming problem `(N, M, t)` (p. 15):
`(N, K(N, M, t), c(N, M, t), E(N, M, t))` with every artist as an agent, `K = M` (the users
with a nonzero column), `c_ij = t_ij` and `E = m = |M|`. -/
noncomputable def assocClaims {n : ℕ} (t : Problem n) : ClaimsProblem (Fin n) ℕ :=
  ⟨Finset.univ, t.support, fun i j => (t j i : ℝ), (t.support.card : ℝ)⟩

end MusicStreaming.Axioms.Supplement


