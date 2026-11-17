-- Prove2me | Definitions.Def_ModFormPIR_Supplement_Fig4
-- name    : ModFormPIR_Supplement_Fig4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:32.748205+00:00
-- url     : https://prove2.me/theorems/d7c08cac-5c42-48b6-92b4-4a85dfd563a8
-- title:
--   The two-server scheme of Fig. 4 over $2^d$ records in $\mathbb F_p$
-- statement:
--   Fix an integer $d\ge2$ with $d\equiv2\pmod 4$ and an odd prime $p>d$, and put $\ell=(d-2)/4$. Records are indexed by $\mathbb F_2^d$ and take values in $\mathbb F_p$. For $x\in\mathbb F_2^d$ let $|x|$ be its Hamming weight, $\pi(x)=|x|\bmod 2$, and
--
--   $$Q(x)=\sum_{1\le i\le j\le d}x_ix_j\in\mathbb F_2 .$$
--
--   1. **Decoding set.** $\mathcal W=\{w:|w|\le\ell\}\cup\{w:|w|\ge d-\ell+1\}$.
--   2. **Coefficients.** $G(x)=\prod_{j=1}^{\ell}\Big(1-\dfrac{|x|+\pi(x)}{4j}\Big)\in\mathbb F_p$ and, for $w\in\mathcal W$, $c_w=\dfrac1{2^d}\sum_{v\in\mathbb F_2^d}G(v)(-1)^{\langle w,v\rangle}$.
--   3. **Preprocess.** Server $t\in\{0,1\}$ stores the truth table of $f_t(x)=\sum_{v}\mathrm{DB}_v(-1)^{Q(x+v)+t\cdot Q(v)}$.
--   4. **Query.** For index $i\in\mathbb F_2^d$ and uniform $r\in\mathbb F_2^d$: $qu_0=r$, $qu_1=r+i$.
--   5. **Answer.** Server $t$ returns $\{\mathrm{Table}_t[qu_t+w]\}_{w\in\mathcal W}$.
--   6. **Reconstruct.** The user outputs
--
--   $$\frac12\sum_{t\in\{0,1\}}\sum_{w\in\mathcal W}c_w(-1)^{Q(r+(t+1)\cdot i+w)+t\cdot Q(i)}\,\mathrm{Table}_t[qu_t+w].$$
--
--   Exponents of $-1$ are computed in $\mathbb F_2$ and the base arithmetic in $\mathbb F_p$. This is the stand-alone two-server scheme with which each server stores exactly as many field elements as the database has records; Theorem 6.1 states its guarantees.
--
--   **Formalization Note** `fig4Record p DB i r` is Reconstruct with the answers $\mathrm{Table}_t[qu_t+w]=f_t(qu_t+w)$ substituted. Inverses in $\mathbb F_p$ are `ZMod.inv`, the field inverse when $p$ is prime; $2^d$, $2$ and $4j$ ($j\le\ell$) are invertible since $p$ is odd and $p>d$. $|x|+\pi(x)$ is a natural number cast into $\mathbb F_p$.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Fig. 4, p.23 (PDF p.27); §6.1 items 1–2, pp.23–24 (PDF pp.27–28)

import Mathlib

open Matrix

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-!
# The two-server scheme of Fig. 4 over `2^d` records in `𝔽_p`

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Fig. 4, p.23 (PDF p.27), and §6.1, pp.23–24 (PDF pp.27–28).

**Formalization Note.**
* Records are indexed by `𝔽₂^d = Fin d → ZMod 2`; the record field is `𝔽_p = ZMod p`. In every statement `p`
  is an odd prime with `p > d`, so the inverses `(2^d)⁻¹`, `(4j)⁻¹` (`j ≤ ℓ`) and `2⁻¹` are the field inverses
  (`ZMod.inv`, which is the field inverse when `p` is prime).
* `(−1)^b` for `b ∈ 𝔽₂` is `(−1) ^ b.val ∈ 𝔽_p` (`sgn`): exponents of `−1` are computed in `𝔽₂`, the base
  arithmetic in `𝔽_p`, as in §6.2.
* `|x|` is the Hamming weight, `π(x) = |x| mod 2`, and `|x| + π(x)` is cast from `ℕ` to `𝔽_p` in `G`.
* The table of server `t ∈ {0, 1} = 𝔽₂` is the truth table `x ↦ f_t(x)`, a function on `𝔽₂^d` (so `2^d`
  elements of `𝔽_p`). Server `t` answers with `Table_t[qu_t + w]` for `w ∈ 𝒲`; `fig4Record` is the user's
  `Reconstruct` with those answers substituted.
-/

variable {d : ℕ}

/-- `Q(x) = ∑_{1 ≤ i ≤ j ≤ d} x_i x_j ∈ 𝔽₂`. -/
def Qform (x : Fin d → ZMod 2) : ZMod 2 :=
  ∑ i : Fin d, ∑ j : Fin d, if i ≤ j then x i * x j else 0

/-- The Hamming weight `|x|`. -/
def hw (x : Fin d → ZMod 2) : ℕ := (Finset.univ.filter fun i => x i ≠ 0).card

/-- `ℓ = (d − 2)/4`. -/
def ell (d : ℕ) : ℕ := (d - 2) / 4

/-- The sparse decoding set `𝒲 = {w : |w| ≤ ℓ} ∪ {w : |w| ≥ d − ℓ + 1}` (§6.1, item 1). -/
def decSet (d : ℕ) : Finset (Fin d → ZMod 2) :=
  Finset.univ.filter fun w => hw w ≤ ell d ∨ d - ell d + 1 ≤ hw w

/-- `(−1)^b ∈ 𝔽_p` for `b ∈ 𝔽₂`. -/
def sgn (p : ℕ) (b : ZMod 2) : ZMod p := (-1) ^ b.val

/-- `G(x) = ∏_{j=1}^{ℓ} (1 − (|x| + π(x))/(4j)) ∈ 𝔽_p`, with `π(x) = |x| mod 2` (§6.1, item 2). -/
def fig4G (p d : ℕ) (x : Fin d → ZMod 2) : ZMod p :=
  ∏ j ∈ Finset.Icc 1 (ell d), (1 - ((hw x + hw x % 2 : ℕ) : ZMod p) * ((4 * j : ℕ) : ZMod p)⁻¹)

/-- The public recovery coefficients `c_w = (1/2^d) ∑_{v ∈ 𝔽₂^d} G(v) (−1)^{⟨w,v⟩}` (§6.1, item 2). -/
def fig4Coeff (p d : ℕ) (w : Fin d → ZMod 2) : ZMod p :=
  ((2 ^ d : ℕ) : ZMod p)⁻¹ * ∑ v : Fin d → ZMod 2, fig4G p d v * sgn p (w ⬝ᵥ v)

/-- Fig. 4, Preprocess: `f_t(x) = ∑_{v ∈ 𝔽₂^d} DB_v (−1)^{Q(x+v) + t·Q(v)}`; `Table_t` is its truth table. -/
def fig4Table (p : ℕ) (t : ZMod 2) (DB : (Fin d → ZMod 2) → ZMod p) (x : Fin d → ZMod 2) : ZMod p :=
  ∑ v : Fin d → ZMod 2, DB v * sgn p (Qform (x + v) + t * Qform v)

/-- Fig. 4, Query: `qu_0 = r`, `qu_1 = r + i`, i.e. `qu_t = r + t·i`. -/
def fig4Query (r i : Fin d → ZMod 2) (t : ZMod 2) : Fin d → ZMod 2 := r + t • i

/-- Fig. 4, Reconstruct with the answers `Table_t[qu_t + w]` (`w ∈ 𝒲`) substituted:
`(1/2) ∑_{t ∈ {0,1}} ∑_{w ∈ 𝒲} c_w (−1)^{Q(r + (t+1)·i + w) + t·Q(i)} Table_t[qu_t + w]`. -/
def fig4Record (p : ℕ) (DB : (Fin d → ZMod 2) → ZMod p) (i r : Fin d → ZMod 2) : ZMod p :=
  ((2 : ℕ) : ZMod p)⁻¹ * ∑ t : ZMod 2, ∑ w ∈ decSet d,
    fig4Coeff p d w * sgn p (Qform (r + (t + 1) • i + w) + t * Qform i) *
      fig4Table p t DB (fig4Query r i t + w)

end Supplement

end ModFormPIR


