-- Prove2me | Definitions.Def_CircTrichotomy_OccComputable
-- name    : CircTrichotomy_OccComputable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:47.17169+00:00
-- url     : https://prove2.me/theorems/837cfe19-0740-4b74-a590-0e808a243d3a
-- title:
--   $\mathrm{Occ}_t$: computing the positions of the $t$ ones of a word
-- statement:
--   For a fixed $t\ge1$, **$\mathrm{Occ}_t$** is the promise problem: given $w\in\{0,1\}^n$ with exactly $t$ ones, output $\mathrm{bin}_\ell(p_0),\dots,\mathrm{bin}_\ell(p_{t-1})$, where $p_0<\cdots<p_{t-1}$ are the positions of the ones, $\ell=\lceil\log_2(n+1)\rceil$, and $\mathrm{bin}_\ell$ writes a number with $\ell$ bits, least significant first.
--
--   $\mathrm{Occ}_t$ is **computable by a circuit family of size $O(f)$ and depth $O(g)$** if there are $n$-circuits $C_n$ over $\{0,1\}$ with $t\ell$ outputs, of size $O(f)$ and depth $O(g)$, whose output $j\ell+b$ is bit $b$ of $p_j$ on every input with exactly $t$ ones. Other inputs are unconstrained.
--
--   **Formalization Note** $\ell$ is `Nat.clog 2 (n + 1)`, the least $\ell$ with $n+1\le2^\ell$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Problem E.1, p.59

import Mathlib
import Definitions.Def_CircTrichotomy_Circuit
import Definitions.Def_CircTrichotomy_BigO

set_option autoImplicit false

namespace CircTrichotomy

/-- The positions `p₀ < p₁ < ⋯` of the letter `1` (`true`) in `w ∈ {0, 1}ⁿ`, in increasing order. -/
def onesPos (n : ℕ) (w : Fin n → Bool) : List ℕ :=
  ((List.finRange n).filter (fun i => w i)).map (fun i => i.val)

/-- **`Occ_t` is computable by a circuit family of size `O(f)` and depth `O(g)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Problem E.1,
p.59): "In this section, binary representations are written least significant bit first. …
bin_ℓ(n) = b₀ … b_{ℓ−1} … n = Σ_{i=0}^{ℓ−1} b_i 2^i. … the following promise problem for each fixed
t ∈ ℕ>0. Problem E.1 (Occ_t). INPUT: A word w ∈ {0, 1}ⁿ, where n ∈ ℕ>0 and |w|₁ = t. OUTPUT: Bit
strings bin_ℓ(p₀), …, bin_ℓ(p_{t−1}) where ℓ = ⌈log(n + 1)⌉ and p_j is the position of the jth
occurrence of 1 in w, with indexing starting at 0." (log is the base-two logarithm, p.58.)

There is a family `(C_n)_{n ∈ ℕ>0}` of `n`-circuits over `{0, 1}` (`Bool`) with `t · ℓ` outputs,
`ℓ = ⌈log₂(n + 1)⌉`, with size `O(f)` and depth `O(g)`, such that on every `w` with exactly `t` ones the
output `j · ℓ + b` is bit `b` (least significant first) of `p_j`. Inputs with `|w|₁ ≠ t` are
unconstrained (promise problem).

**Formalization Note** `Nat.clog 2 (n + 1)` is the least `ℓ` with `n + 1 ≤ 2^ℓ`, i.e.
`⌈log₂(n + 1)⌉`. The outputs are `f_C(w) = eval(w, out(0)) ⋯ eval(w, out(tℓ − 1))` (Definition A.2), so
output `j · ℓ + b` is the `b`-th bit of the `j`-th string. -/
def OccComputable (t : ℕ) (f g : ℕ → ℝ) : Prop :=
  ∃ C : ∀ n : ℕ, 0 < n → Circuit Bool n (t * Nat.clog 2 (n + 1)),
    BigO (famSize C) f ∧ BigO (famDepth C) g ∧
    ∀ (n : ℕ) (h : 0 < n) (w : Fin n → Bool), (onesPos n w).length = t →
      ∀ o : Fin (t * Nat.clog 2 (n + 1)),
        ((C n h).output w o ↔
          ((onesPos n w).getD (o.val / Nat.clog 2 (n + 1)) 0).testBit
            (o.val % Nat.clog 2 (n + 1)) = true)

end CircTrichotomy


