-- Prove2me | Definitions.Def_LinMaxLoad_Supplement_loadProb
-- name    : LinMaxLoad_Supplement_loadProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:59.500045+00:00
-- url     : https://prove2.me/theorems/1a784f3b-6b03-4c66-9e6b-955208e00ec3
-- title:
--   Linear max load probability $q_k(S) = \Pr_h[M(S,h) \le k]$
-- statement:
--   Let $p$ be a prime, $S \subseteq \mathbb F_p^u$ a finite set, $k \ge 0$ an integer, $\ell = \lceil \log_p |S| \rceil$, and $h : \mathbb F_p^u \to \mathbb F_p^{\ell}$ a uniformly random linear map. The **linear max load probability** of $S$ is
--
--   $$
--   q_k(S) := \Pr_h\bigl[M(S, h) \le k\bigr],
--   $$
--
--   the probability that no bin receives more than $k$ points of $S$. The assumption $q_k(S) = \Omega(1)$ drives the energy and covering results (Theorem 16 of the paper).
--
--   **Formalization Note** $\ell = \lceil \log_p |S| \rceil$ is `Nat.clog p S.card` and the probability is over all linear maps $\mathbb F_p^u \to \mathbb F_p^\ell$, the conventions of the published definitions `LinMaxLoad.linMaxLoad` and `LinMaxLoad.probLin`.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2, item 5, p.3

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Linear max load probability** `q_k(S) := Pr_h[M(S, h) ≤ k]` (Definition 2, item 5, p.3,
of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
where `S ⊆ F_p^u` is finite, `ℓ = ⌈log_p |S|⌉` and `h : F_p^u → F_p^ℓ` is a uniformly random
linear map.

**Formalization Note** `F_p^u` is `Fin u → ZMod p`, `ℓ = ⌈log_p |S|⌉` is `Nat.clog p S.card`
(the convention of the published `LinMaxLoad.linMaxLoad`), and `Pr_h` is the published
`LinMaxLoad.probLin`, the uniform distribution over all linear maps. -/
noncomputable def loadProb (p u : ℕ) [Fact p.Prime] (k : ℕ) (S : Finset (Fin u → ZMod p)) : ℝ :=
  probLin (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card)
    fun h => maxLoad (h : (Fin u → ZMod p) → Fin (Nat.clog p S.card) → ZMod p) S ≤ k

end LinMaxLoad.Supplement


