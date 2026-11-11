-- Prove2me | Definitions.Def_ProdMomentConc_Lk
-- name    : ProdMomentConc_Lk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:12.809571+00:00
-- url     : https://prove2.me/theorems/8adb462a-d8ed-4015-8251-35f03a5746fe
-- title:
--   $L_k$, the number of underlying variables read by a set of outputs
-- statement:
--   For a set $S \subseteq [n]$ of outputs, let
--
--   $$
--   L(S) := \Big|\bigcup_{i \in S} P_i\Big|
--   $$
--
--   be the number of left vertices of the dependency graph adjacent to $S$, i.e. the number of underlying variables read by at least one output in $S$. The paper's random variable $L_k = |\Gamma(I)|$ is $L(I)$ for the uniformly random $k$-subset $I$.
--
--   The event $L_k > r$ is one of the two bad events of the main theorem: on its complement the outputs in $I$ depend on at most $r$ underlying variables, which are then mutually independent.
--
--   **Formalization Note** $L$ is defined as a function of the subset; the random variable is obtained by evaluating it under `kSubsetLaw n k`.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §3.2, p.15 (PDF p.15), "let Lk = |Γ(I)| … denote the number of left vertices … in the subgraph induced by I"

import Mathlib

namespace ProdMomentConc

/-- **`L_k`: the number of left vertices adjacent to a set of outputs.**
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), §3.2, p.15: "let
Lk = |Γ(I)| … denote the number of left vertices … in the subgraph induced by I".

For a set `S` of outputs, `Lk P S = |⋃_{i ∈ S} P i|`, the number of underlying variables read by
some output in `S`.

**Formalization Note.** `Lk P` is a function of the set `S`; the paper's `L_k` is this function
evaluated at the uniformly random `k`-subset `I`. -/
def Lk {m n : ℕ} (P : Fin n → Finset (Fin m)) (S : Finset (Fin n)) : ℕ :=
  (S.biUnion P).card

end ProdMomentConc


