-- Prove2me | Definitions.Def_CircTrichotomy_approxK
-- name    : CircTrichotomy_approxK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:59.970203+00:00
-- url     : https://prove2.me/theorems/ddafc23c-af3d-48b4-865e-cedb4ab9a013
-- title:
--   The congruence $\approx_k$ of the $O(1)$-characterization
-- statement:
--   For $k\ge1$ and $u,v\in\Sigma^+$, $u\approx_k v$ if $u=v$, or
--   1. $|u|,|v|>2k$;
--   2. $u=u'xu''$ and $v=v'yv''$ with the same length-$k$ prefix $u'=v'$ and the same length-$k$ suffix $u''=v''$;
--   3. $|x|\equiv|y|\pmod k$;
--   4. $x$ and $y$ have the same set of letters in each residue class of positions modulo $k$: $\mathrm{cont}_{i,k}(x)=\mathrm{cont}_{i,k}(y)$ for all $i\in[0,k-1]$.
--
--   Regular languages of constant circuit size are exactly the unions of $\approx_k$-classes.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (4), p.3

import Mathlib
import Definitions.Def_CircTrichotomy_piMod

set_option autoImplicit false

namespace CircTrichotomy

/-- **`≈_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (4), p.3): "≈_k denotes the following congruence on Σ⁺: u ≈_k v
if, and only if, u = v or
• |u|, |v| > 2k,
• u = u′xu″ and v = v′yv″ have the same k-length prefix u′ = v′ and the same k-length suffix
  u″ = v″,
• |x| ≡ |y| mod k, and
• x and y agree on the set of letters appearing in positions that are equivalent mod k."

Here `x = κ_k(u)` and `y = κ_k(v)` are the middle factors, and the last bullet is
`cont_{i,k}(x) = cont_{i,k}(y)` for every residue `i ∈ [0, k − 1]` (positions counted inside `x` and
`y`; since `|u′| = |v′| = k` this is the same residue inside `u` and `v`). -/
def approxK {α : Type} (k : ℕ) (u v : List α) : Prop :=
  u = v ∨
    (2 * k < u.length ∧ 2 * k < v.length ∧ u.take k = v.take k ∧
      u.drop (u.length - k) = v.drop (v.length - k) ∧
      (kappa k u).length % k = (kappa k v).length % k ∧
      ∀ i < k, contMod k i (kappa k u) = contMod k i (kappa k v))

end CircTrichotomy


