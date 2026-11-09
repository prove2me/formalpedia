-- Prove2me | Definitions.Def_LinMaxLoad_linMaxLoad
-- name    : LinMaxLoad_linMaxLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:56.539845+00:00
-- url     : https://prove2.me/theorems/01c1f48a-a7d6-422a-9f34-8faf5bb64311
-- title:
--   Expected linear max load $m(S)$
-- statement:
--   Let $p$ be a prime and $S \subseteq \mathbb F_p^u$ a finite set. Put $\ell = \lceil \log_p |S| \rceil$, the least $\ell$ with $|S| \le p^\ell$, so that $\mathbb F_p^\ell$ has at least as many bins as $S$ has points. The **expected linear max load** of $S$ is
--
--   $$
--   m(S) := \mathbb E_h\big[M(S, h)\big],
--   $$
--
--   where $h : \mathbb F_p^u \to \mathbb F_p^\ell$ is a uniformly random linear map and $M(S,h)$ is the max load. Small $m(S)$ means that linear hashing spreads $S$ almost as well as a fully random function would; the paper relates it to the additive structure of $S$.
--
--   **Formalization Note** $\mathbb F_p^u$ is `Fin u → ZMod p` and $\ell$ is `Nat.clog p |S|` (so $\ell = 0$ when $|S| \le 1$). Definition 2 opens with "a set of size $p^\ell$" but immediately sets $\ell = \lceil \log_p |S|\rceil$, and Theorem 17 and its proof apply $m(S)$ to sets of arbitrary size; the definition therefore covers every finite $S$.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2 item 3, p.3 (ℓ = ⌈log_p |S|⌉ as in the proof of Theorem 17, p.24)

import Mathlib
import Definitions.Def_LinMaxLoad_expLoad

namespace LinMaxLoad

/-- **Expected linear max load** `m(S) := E_h[M(S, h)]` (Definition 2, item 3, p.3, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
where `S ⊆ F_p^u` is finite, `ℓ = ⌈log_p |S|⌉` and `h : F_p^u → F_p^ℓ` is a uniformly random
linear map.

**Formalization Note** `F_p^u` is `Fin u → ZMod p` and `ℓ = ⌈log_p |S|⌉` is
`Nat.clog p S.card` (so `ℓ = 0` for `|S| ≤ 1`). Definition 2 opens with "a set of size `p^ℓ`"
but immediately sets `ℓ = ⌈log_p |S|⌉`, and Theorem 17 and its proof (pp.23–24) apply `m(S)` to
sets of arbitrary size; the definition therefore covers every finite `S`. -/
noncomputable def linMaxLoad (p u : ℕ) [Fact p.Prime] (S : Finset (Fin u → ZMod p)) : ℝ :=
  expLoad (ZMod p) (Fin u → ZMod p) (Nat.clog p S.card) S

end LinMaxLoad


