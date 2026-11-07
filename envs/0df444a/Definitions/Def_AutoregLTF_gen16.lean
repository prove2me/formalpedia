-- Prove2me | Definitions.Def_AutoregLTF_gen16
-- name    : AutoregLTF_gen16
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:18.120799+00:00
-- url     : https://prove2.me/theorems/4901f33f-ce6f-4703-8653-869e05d82480
-- title:
--   The single recurrence (16) and the history $(0,E^t_{\theta,i})$
-- statement:
--   For integers $B$ and $a_1,\dots,a_{p+1}$, recurrence (16) is
--
--   $$z_n=\mathbf 1\Big\{-B+\sum_{\ell=1}^{p+1}a_\ell z_{n-\ell}\ge0\Big\}.$$
--
--   For $i\in[m]$ and $t\ge0$, the **history** $(0,E^t_{\theta,i})$ is the initial segment $z_{-p-1}=0$, $z_{-p+r}=E^t_{\theta,i,r}$ ($0\le r<p$). For $d\ge p+1$, (16) is recurrence (1) with $w_\ell=a_\ell/B$ for $\ell\le p+1$ and $w_\ell=0$ otherwise.
--
--   **Formalization Note** `gen16 P B a h k` is $z_{k-P-1}$: the history occupies `h 0, …, h P`, and the generated bits $z_0,\dots,z_{P-1}$ are `gen16 P B a h (P + 1 + r)`. `hist m θ i t` is the history $(0,E^t_{\theta,i})$ in that indexing.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §3, (16) and the history, p.8

import Mathlib
import Definitions.Def_AutoregLTF_block

namespace AutoregLTF

/-!
# The single recurrence (16) and the history `(0, E^t_{θ,i})`

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §3, (16), p.8.

`z_n = 1{−B + ∑_{ℓ=1}^{p+1} a_ℓ z_{n−ℓ} ≥ 0}`. "For `i ∈ [m]` and `t ≥ 0`, the history
`(0, E^t_{θ,i})` denotes the initial values `z_{−p−1} = 0` and `z_{−p+r} = E^t_{θ,i,r}` for
`0 ≤ r < p`."

**Formalization Note.**
* `gen16 P B a h k` is `z_{k−P−1}`: the `P + 1` initial values `z_{−P−1}, …, z_{−1}` are `h 0, …, h P`,
  and for `k ≥ P + 1` (`n = k − P − 1 ≥ 0`) the value is given by (16) with window `P + 1`. The next
  `P` bits `z_0, …, z_{P−1}` are `gen16 P B a h (P + 1 + r)`, `0 ≤ r < P`.
* The coefficients are `a : ℕ → ℤ`, read at `ℓ ∈ [P + 1]`; `B` is an integer.
-/

/-- The recurrence (16) with window `P + 1` from the history `h` (`h k = z_{k−P−1}` for `k ≤ P`):
`gen16 P B a h k = z_{k−P−1}`. -/
def gen16 (P : ℕ) (B : ℤ) (a : ℕ → ℤ) (h : ℕ → Bool) (k : ℕ) : Bool :=
  if k ≤ P then h k
  else decide (0 ≤ -B + ∑ ℓ : Fin (P + 1),
    a (ℓ.val + 1) * ((gen16 P B a h (k - (ℓ.val + 1))).toNat : ℤ))
termination_by k
decreasing_by omega

/-- The history `(0, E^t_{θ,i})` of p.8 in the indexing of `gen16 (p m)`: position `0` is
`z_{−p−1} = 0` and position `1 + r` is `z_{−p+r} = E^t_{θ,i,r}` (`0 ≤ r < p`). -/
def hist (m : ℕ) (θ : ℕ → ℤ) (i t : ℕ) (k : ℕ) : Bool :=
  if k = 0 then false else E m θ i t (k - 1)

end AutoregLTF


