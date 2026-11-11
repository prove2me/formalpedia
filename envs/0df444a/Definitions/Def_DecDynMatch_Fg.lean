-- Prove2me | Definitions.Def_DecDynMatch_Fg
-- name    : DecDynMatch_Fg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:22.75337+00:00
-- url     : https://prove2.me/theorems/2a2c74a5-7cc3-4a15-845c-c3686d823a59
-- title:
--   The replay rule $F_g$ of a growth function $g$, and $N_g(T)$
-- statement:
--   For a function $g$ on positive integers define
--   $$
--   s_0=H,\qquad s_{j+1}=s_j+g(s_j)\quad(j\ge 0),
--   $$
--   $$
--   F_g(x)=H+2x+\max\Bigl(\{\,g(s_j)-s_j : j\ge 0,\ 64s_j\le x\,\}\cup\{0\}\Bigr)\quad(x\ge 1),
--   $$
--   and $N_g(T)=\#\{\,j\ge 0 : s_j<T\,\}$. The protocol $\Pi_g$ is SC-DA with replay rule $F_g$; for $g(t)=t$ it is SC-DA itself. The mission uses these objects only at $g(t)=t$, to state the specialization from which Theorem 1 follows.
--
--   **Formalization Note** The maximum is a `Finset.sup` in `ℕ` of truncated differences $g(s_j)\dot- s_j$ over $j\le x$; truncating negative differences does not change a maximum that contains $0$, and for $g\ge 1$ the condition $64s_j\le x$ forces $j\le x$. $N_g$ counts over $j<T$, which loses nothing for $g\ge1$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (5), p.8; eq. (6), p.9

import Mathlib
import Definitions.Def_DecDynMatch_J

namespace DecDynMatch

/-- The sequence `s₀ = H`, `s_{j+1} = s_j + g(s_j)` of eq. (5), p.8. -/
def sseq (K : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => H K
  | j + 1 => sseq K g j + g (sseq K g j)

/-- **The replay rule `F_g` of a growth function `g`.** J. Chen, M. Gao, Z. Zhang, *Decentralized
Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (5), p.8:
"s₀ = H, s_{j+1} = s_j + g(s_j) ∀ j ≥ 0,
F_g(x) = H + 2x + max({g(s_j) − s_j : j ≥ 0, 64 s_j ≤ x} ∪ {0}) ∀ x ≥ 1."

**Formalization Note.** The maximum is a `Finset.sup` in `ℕ` (whose bottom is `0`, the `∪ {0}`)
of truncated differences `g(s_j) − s_j`; truncating negative differences at `0` does not change a
maximum that already contains `0`. The indices are taken over `j ≤ x`: for `g ≥ 1` on positive
integers, `s_j ≥ H + j`, so `64 s_j ≤ x` forces `j ≤ x`. -/
def Fg (K : ℕ) (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  H K + 2 * x +
    ((Finset.range (x + 1)).filter (fun j => 64 * sseq K g j ≤ x)).sup
      (fun j => g (sseq K g j) - sseq K g j)

/-- `N_g(T) = #{j ≥ 0 : s_j < T}` (eq. (6), p.9). The indices are taken over `j < T`, which loses
nothing when `g ≥ 1` on positive integers (then `s_j > j`). -/
def Ng (K : ℕ) (g : ℕ → ℕ) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun j => sseq K g j < T)).card

end DecDynMatch


