-- Prove2me | Definitions.Def_TenChallenges_Challenge_04
-- name    : TenChallenges_Challenge_04
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:39:34.917066+00:00
-- url     : https://prove2.me/theorems/e114bc97-a76d-4b7b-a3ac-3ad080f07619
-- title:
--   Challenge 4: Sidorenko's conjecture for bipartite graphs with sides of size at most $r$
-- statement:
--   The scaled form of Challenge 4. For a natural number $r$, $\mathrm{Sid}(r)$ says: for every finite graph $H$ which is bipartite with both sides of size at most $r$, and every finite graph $G$ with at least one vertex,
--
--   $$t(H,G)\ \ge\ t(K_2,G)^{\,e(H)}.$$
--
--   Here $t$ is the homomorphism density and $e(H)$ the number of edges of $H$. The rungs $r\le 4$ follow from Sidorenko's theorem for bipartite graphs with at most four vertices on one side; $r=5$ is open.
--
--   **Formalization Note.** Vertex types of $H$ and $G$ range over finite types in the lowest universe; the host graph is required to be nonempty.
-- source:
--   Ten Challenges repository, file Challenges/challenge_04.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Challenges/challenge_04.lean; V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 4.

import Definitions.Def_TenChallenges_Sidorenko

open SimpleGraph

namespace TenChallenges

/-- Sidorenko's inequality for bipartite graphs with at most `r` vertices in each side. -/
def statement_04 (r : ℕ) : Prop :=
  ∀ {W V : Type} [Fintype W] [Fintype V] [Nonempty V]
    (H : SimpleGraph W) (G : SimpleGraph V),
    BipartiteBoundedBy H r → SidorenkoFor H G

end TenChallenges


