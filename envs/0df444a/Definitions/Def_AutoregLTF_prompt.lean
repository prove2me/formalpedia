-- Prove2me | Definitions.Def_AutoregLTF_prompt
-- name    : AutoregLTF_prompt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:19.073206+00:00
-- url     : https://prove2.me/theorems/09907333-9648-4b05-839d-692bdaee2cad
-- title:
--   The label-free prompts $x^{i,s}$ (33)–(35), the weights (36), and the trajectory $z^{(i)}$ (37)–(38)
-- statement:
--   Assume $d\ge p+1$. For $i\in[m]$ the string $E_i=0^{d-p}E^0_iE^1_i$, indexed by $1-d\le n\le p$ (33), consists of $d-p$ zeros followed by the first two blocks of row $i$. For a column $s\in[m]$ let
--
--   $$r_s=(\pi(\mathrm{out},s)-T+1)\bmod p\qquad(34),\qquad x^{i,s}_n=(E_i)_{r_s+n}\quad(1-d\le n\le0)\qquad(35).$$
--
--   By Lemma 1 the blocks $E^0_i,E^1_i$ do not depend on the labeling, so neither do the $m^2$ prompts. Given integers $B$ and $a_1,\dots,a_{p+1}$, the weights (36) are $w_\ell=a_\ell/B$ for $1\le\ell\le p+1$ and $w_\ell=0$ for $p+1<\ell\le d$. The trajectory $z^{(i)}$ of (37)–(38) is recurrence (1) started from the prompt $0^{d-p}E^0_{\theta,i}$.
--
--   **Formalization Note** `prompt m d T i s` builds $x^{i,s}$ from the blocks of the all-zero labeling; it takes no labeling. `rs` uses the integer residue in $\{0,\dots,p-1\}$. `zAt w x n` is $z_n$ of (1) with the paper's time index ($n\ge1-d$), `prompt0 m d θ i` is $0^{d-p}E^0_{\theta,i}$, and `wOf d p B a` is (36).
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §4, (33)–(36) pp.11–12, (37)–(38) p.12

import Mathlib
import Definitions.Def_AutoregLTF_ltf
import Definitions.Def_AutoregLTF_block

namespace AutoregLTF

/-!
# The prompts (33)–(35) and the weights (36)

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §4, (33)–(36),
pp.11–12.

For `i ∈ [m]`, the string `E_i = ((E_i)_n)_{n=1−d}^{p}` is `0^{d−p} E^0_i E^1_i`: `(E_i)_n = 0` for
`1 − d ≤ n ≤ −p`, `(E^0_i)_{n+p−1}` for `1 − p ≤ n ≤ 0`, `(E^1_i)_{n−1}` for `1 ≤ n ≤ p` (33). For a
column `s ∈ [m]`, `r_s = (π(out, s) − T + 1) mod p` (34), and the prompt is
`x^{i,s}_n = (E_i)_{r_s+n}` for `1 − d ≤ n ≤ 0` (35). The weights are `w_ℓ = a_ℓ/B` for
`1 ≤ ℓ ≤ p + 1` and `0` for `p + 1 < ℓ ≤ d` (36).

**Formalization Note.**
* The prompts are built from the blocks `E^0_{θ,i}`, `E^1_{θ,i}` at the encoding `θ = 0` (the
  encoding of the all-zero labeling). By Lemma 1 (second assertion) these blocks are the same for every
  labeling, so these are the paper's prompts for every `λ`; they take no labeling as an argument.
* `strE m d i n` is `(E_i)_n` for `n ∈ ℤ`; it is `false` outside `1 − d ≤ n ≤ p`, where the paper does
  not define it ((35) never reads there when `d ≥ p + 1`).
* `rs m T s` is the integer residue in `{0, …, p − 1}` (`Int.emod`, the paper's `mod`).
* A prompt is `Fin d → Bool` in the orientation of `ltf`: index `k` holds `x^{i,s}_{k+1−d}`.
* `wOf d P B a` is (36) with `P = p`, for any integers `B` and `a_1, …, a_{p+1}`; `w ⟨ℓ, _⟩ = w_{ℓ+1}`.
-/

/-- The label-free string `E_i = 0^{d−p} E^0_i E^1_i` of (33), as `n ↦ (E_i)_n`. -/
def strE (m d i : ℕ) (n : ℤ) : Bool :=
  if n < 1 - (d : ℤ) then false
  else if n ≤ -(p m : ℤ) then false
  else if n ≤ 0 then E m (fun _ => 0) i 0 (n + p m - 1).toNat
  else if n ≤ (p m : ℤ) then E m (fun _ => 0) i 1 (n - 1).toNat
  else false

/-- The shift `r_s = (π(out, s) − T + 1) mod p` of (34). -/
def rs (m T s : ℕ) : ℤ :=
  ((piOut m s : ℤ) - T + 1) % (p m : ℤ)

/-- The prompt `x^{i,s}` of (35): `x^{i,s}_n = (E_i)_{r_s+n}` for `1 − d ≤ n ≤ 0`; index `k` of the
`Fin d → Bool` vector is `n = k + 1 − d`. -/
def prompt (m d T i s : ℕ) : Fin d → Bool :=
  fun k => strE m d i (rs m T s + ((k.val : ℤ) + 1 - d))

/-- The weights (36): `w_ℓ = a_ℓ/B` for `1 ≤ ℓ ≤ P + 1` and `0` for `P + 1 < ℓ ≤ d`, with
`w ⟨ℓ, _⟩ = w_{ℓ+1}`. -/
def wOf (d P : ℕ) (B : ℤ) (a : ℕ → ℤ) : Fin d → ℚ :=
  fun ℓ => if ℓ.val + 1 ≤ P + 1 then ((a (ℓ.val + 1) : ℚ) / (B : ℚ)) else 0

/-- The free-running trajectory `z^{(i)}` of (37)–(38) and of (1), read with the paper's indices:
`zAt w x n = z_n` for `n ≥ 1 − d`, where `z` is the trajectory of (1) from the prompt `x`. -/
def zAt {d : ℕ} (w : Fin d → ℚ) (x : Fin d → Bool) (n : ℤ) : Bool :=
  traj w x (n + d - 1).toNat

/-- The prompt `0^{d−p} E^0_{θ,i}` of (37), for an encoding `θ`: index `k` holds `z^{(i)}_{k+1−d}`. -/
def prompt0 (m d : ℕ) (θ : ℕ → ℤ) (i : ℕ) : Fin d → Bool :=
  fun k => if (k.val : ℤ) + 1 - d ≤ -(p m : ℤ) then false
    else E m θ i 0 ((k.val : ℤ) + 1 - d + p m - 1).toNat

end AutoregLTF


