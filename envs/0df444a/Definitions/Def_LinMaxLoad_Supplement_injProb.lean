-- Prove2me | Definitions.Def_LinMaxLoad_Supplement_injProb
-- name    : LinMaxLoad_Supplement_injProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:37.246031+00:00
-- url     : https://prove2.me/theorems/4e01049a-5384-4a66-ac5d-5637c5c03cb1
-- title:
--   Injectivity probability $q(S) = \Pr_h[M(S,h) = 1]$
-- statement:
--   Let $p$ be a prime, $S \subseteq \mathbb F_p^u$ a finite set, $\ell = \lceil \log_p |S| \rceil$, and $h : \mathbb F_p^u \to \mathbb F_p^{\ell}$ a uniformly random linear map. The **injectivity probability** of $S$ is
--
--   $$
--   q(S) := \Pr_h\bigl[M(S, h) = 1\bigr],
--   $$
--
--   the probability that $h$ maps the points of $S$ to pairwise distinct values (here $M(S,h)$ is the max load). Sets with $q(S) = \Omega(1)$ are classified in Theorems 12–14 of the paper.
--
--   **Formalization Note** $\ell = \lceil \log_p |S| \rceil$ is `Nat.clog p S.card` and the probability is over all linear maps $\mathbb F_p^u \to \mathbb F_p^\ell$, the conventions of the published definitions `LinMaxLoad.linMaxLoad` and `LinMaxLoad.probLin`. For $S = \emptyset$ the max load is $0$, so $q(\emptyset) = 0$.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2, item 4, p.3

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Injectivity probability** `q(S) := Pr_h[M(S, h) = 1]` (Definition 2, item 4, p.3, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
where `S ⊆ F_p^u` is finite, `ℓ = ⌈log_p |S|⌉` and `h : F_p^u → F_p^ℓ` is a uniformly random
linear map.

**Formalization Note** `F_p^u` is `Fin u → ZMod p`, `ℓ = ⌈log_p |S|⌉` is `Nat.clog p S.card`
(the convention of the published `LinMaxLoad.linMaxLoad`), and `Pr_h` is the published
`LinMaxLoad.probLin`, the uniform distribution over all linear maps. For `S = ∅` the max load
is `0`, so `q(∅) = 0`. -/
noncomputable def injProb (p u : ℕ) [Fact p.Prime] (S : Finset (Fin u → ZMod p)) : ℝ :=
  probLin (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
    fun h => maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p) S = 1

end LinMaxLoad.Supplement


