-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_ApproxAccess
-- name    : CaiFourierSparse_Learning_ApproxAccess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:12:09.854201+00:00
-- url     : https://prove2.me/theorems/a0f08ca1-6320-4568-9bbc-6a798ce25eb1
-- title:
--   Haar types, the folded signal $\zeta_w$, the density $p_\ell$ and the law and output of Function ApproxAccess
-- statement:
--   For $K=2^a$ the **Haar types** $W$ (`haarTypes`) are the scaling type (support $\ell=K$) and the wavelet types of support $\ell=2^m$, $1\le m\le a$ (`typeLen`). For $b\in\mathbb Z$, $w_b$ is the type shifted to the support $b\ell+[\ell]$ (`wShift`) and $\varphi_{w_b}(t)=\frac1{\sqrt2}\sum_n w_b[n](-1)^ne^{i\pi nt}$ (`phiWB`), $\varphi_w=\varphi_{w_0}$ (`phiW`). Arguments are reduced modulo $2$ into $[-1,1)$ (`red`); the fibre of $u$ is $\{t_a=(u+2a)/\ell \bmod 2: a\in[\ell]\}$ (`fibre`). The **folded signal** of eq. (52) is
--   $$\zeta_w(u)=\frac{\sqrt2}{\ell}\sum_{a\in[\ell]}y(t_a)\,\overline{\varphi_w(t_a)}\qquad(\texttt{zeta}).$$
--   The density of eq. (54) is $p_\ell(t)=2^j/\log_2\ell$ if $|t|\in(1-2^{-j},1-2^{-j-1}]$ with $j\in[\log_2\ell-1]$, and $(\ell/4)/\log_2\ell$ if $|t|>1-2/\ell$ (`pEll`). **ApproxAccess**$(w,\ell,R,u)$ draws, in each of $R$ independent rounds, $j$ uniform in $[\log_2\ell]$ and then $u_r$ uniform among the fibre points in $J\cup-J$, where $J=(1-2^{-j},1-2^{-j-1}]$ if $j<\log_2\ell-1$ and $J=(1-2/\ell,1]$ otherwise (`inJ`, `roundLaw`; if that set is empty the round has no outcome, which appears as missing mass); the joint law of $(u_r)_{r<R}$ is the product (`approxAccessLaw`), and the output is
--   $$\tilde z(u)=\frac1R\sum_{r<R}\frac{y(u_r)\,\overline{\varphi_w(u_r)}}{\sqrt2\,p_\ell(u_r)}\qquad(\texttt{approxAccessOut}).$$
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Algorithm 1 lines 1–10 and eqs. (52), (54), printed pp. 25–26 (PDF pp. 27–28)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal

namespace CaiFourierSparse.Learning

open MeasureTheory Complex
open scoped ENNReal

/-! # Haar types, the folded signal `ζ_w`, the density `p_ℓ` and Function `ApproxAccess`
(Cai–Chen–Shao–Wang, Algorithm 1 lines 1–10, eqs. (52), (54), §5)

For `K = 2^a`, the set `W` of Haar types has `log₂ K + 1` elements: the scaling type `H^sc_{[K]}`
of support `ℓ = K` and the wavelet types `H^wav_{[ℓ]}` of support `ℓ = 2^m`, `1 ≤ m ≤ a`. For a type
`w` of support `ℓ` and `b ∈ ℤ`, `w_b` is `w` shifted to the support `bℓ + [ℓ]`, and
`φ_{w_b}(t) = (1/√2) ∑_n w_b[n] (-1)^n e^{iπ n t}`. Sample arguments are reduced modulo 2 into
`[-1,1)`. -/

/-- The Haar types `W` for `K = 2^a`: `none` is the scaling type, `some m` (`1 ≤ m ≤ a`) the
wavelet type of support `2^m`. -/
def haarTypes (a : ℕ) : Finset (Option ℕ) :=
  insert none ((Finset.Icc 1 a).image some)

/-- Support size `ℓ` of a type: `K = 2^a` for the scaling type, `2^m` for a wavelet type. -/
def typeLen (a : ℕ) (w : Option ℕ) : ℕ :=
  match w with
  | none => 2 ^ a
  | some m => 2 ^ m

/-- The shifted Haar vector `w_b` (support `bℓ + [ℓ]`), as a function on `ℤ`. -/
noncomputable def wShift (a : ℕ) (w : Option ℕ) (b n : ℤ) : ℝ :=
  let ℓ : ℤ := typeLen a w
  match w with
  | none => if b * ℓ ≤ n ∧ n < b * ℓ + ℓ then 1 / Real.sqrt (ℓ : ℝ) else 0
  | some _ =>
    if b * ℓ ≤ n ∧ n < b * ℓ + ℓ / 2 then 1 / Real.sqrt (ℓ : ℝ)
    else if b * ℓ + ℓ / 2 ≤ n ∧ n < b * ℓ + ℓ then -1 / Real.sqrt (ℓ : ℝ) else 0

/-- `φ_{w_b}(t) = (1/√2) ∑_{n ∈ bℓ + [ℓ]} w_b[n] (-1)^n e^{iπ n t}`. -/
noncomputable def phiWB (a : ℕ) (w : Option ℕ) (b : ℤ) (t : ℝ) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) *
    ∑ n ∈ Finset.Ico (b * (typeLen a w : ℤ)) (b * (typeLen a w : ℤ) + typeLen a w),
      (wShift a w b n : ℂ) * (-1 : ℂ) ^ n.natAbs *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))

/-- `φ_w = φ_{w_0}`. -/
noncomputable def phiW (a : ℕ) (w : Option ℕ) (t : ℝ) : ℂ := phiWB a w 0 t

/-- Reduction modulo 2 into `[-1, 1)`. -/
noncomputable def red (t : ℝ) : ℝ := t - 2 * (Int.floor ((t + 1) / 2) : ℝ)

/-- The `ℓ` fibre points `t_a = ((u + 2a)/ℓ mod 2) ∈ [-1,1)`, `a ∈ [ℓ]`. -/
noncomputable def fibre (ℓ : ℕ) (u : ℝ) : Finset ℝ :=
  (Finset.range ℓ).image fun i : ℕ => red ((u + 2 * (i : ℝ)) / (ℓ : ℝ))

/-- The folded signal of eq. (52):
`ζ_w(u) = (√2/ℓ) ∑_{a ∈ [ℓ]} y(t_a) · conj(φ_w(t_a))`, `t_a = (u + 2a)/ℓ mod 2`. -/
noncomputable def zeta (a : ℕ) (w : Option ℕ) (y : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((Real.sqrt 2 / typeLen a w : ℝ) : ℂ) * ∑ i ∈ Finset.range (typeLen a w),
    y (red ((u + 2 * (i : ℝ)) / (typeLen a w : ℝ))) *
      (starRingEnd ℂ) (phiW a w (red ((u + 2 * (i : ℝ)) / (typeLen a w : ℝ))))

/-- The density `p_ℓ` of eq. (54): `2^j / log₂ ℓ` if `|t| ∈ (1 - 2^{-j}, 1 - 2^{-j-1}]` for
`j ∈ [log₂ ℓ - 1]`, and `(ℓ/4)/log₂ ℓ` if `|t| > 1 - 2/ℓ`. -/
noncomputable def pEll (ℓ : ℕ) (t : ℝ) : ℝ :=
  let L : ℝ := Nat.log 2 ℓ
  if 1 - 2 / (ℓ : ℝ) < |t| then ((ℓ : ℝ) / 4) / L
  else ∑ j ∈ Finset.range (Nat.log 2 ℓ - 1),
    if 1 - (2 : ℝ) ^ (-(j : ℤ)) < |t| ∧ |t| ≤ 1 - (2 : ℝ) ^ (-(j : ℤ) - 1)
    then (2 : ℝ) ^ j / L else 0

/-- The interval `J ∪ -J` of Algorithm 1, line 5, for `j ∈ [log₂ ℓ]`:
`J = (1 - 2^{-j}, 1 - 2^{-j-1}]` if `j < log₂ ℓ - 1`, and `J = (1 - 2/ℓ, 1]` otherwise. -/
def inJ (ℓ j : ℕ) (t : ℝ) : Prop :=
  if j + 1 < Nat.log 2 ℓ then
    1 - (2 : ℝ) ^ (-(j : ℤ)) < |t| ∧ |t| ≤ 1 - (2 : ℝ) ^ (-(j : ℤ) - 1)
  else 1 - 2 / (ℓ : ℝ) < |t| ∧ |t| ≤ 1

open Classical in
/-- The law of one sample `u_r` of `ApproxAccess` (lines 4–6): `j` uniform in `[log₂ ℓ]`, then
`u_r` uniform among the fibre points of `u` lying in `J ∪ -J`. If that set is empty the round has
no outcome, which shows up as missing mass. -/
noncomputable def roundLaw (ℓ : ℕ) (u : ℝ) : Measure ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 ℓ),
    ((Nat.log 2 ℓ : ℝ≥0∞)⁻¹ * (((fibre ℓ u).filter (inJ ℓ j)).card : ℝ≥0∞)⁻¹) •
      ∑ t ∈ (fibre ℓ u).filter (inJ ℓ j), Measure.dirac t

/-- The joint law of the `R` independent samples `u_0, …, u_{R-1}` drawn by
`ApproxAccess(w, ℓ, R, u)`. -/
noncomputable def approxAccessLaw (ℓ R : ℕ) (u : ℝ) : Measure (Fin R → ℝ) :=
  Measure.pi (fun _ : Fin R => roundLaw ℓ u)

/-- The output `z̃(u) = (1/R) ∑_{r ∈ [R]} y(u_r) · conj(φ_w(u_r)) / (√2 · p_ℓ(u_r))` of
`ApproxAccess(w, ℓ, R, u)` on the samples `(u_r)_r` (lines 7 and 9). -/
noncomputable def approxAccessOut (a : ℕ) (w : Option ℕ) (y : ℝ → ℂ) (R : ℕ)
    (us : Fin R → ℝ) : ℂ :=
  ((R : ℂ))⁻¹ * ∑ r, y (us r) * (starRingEnd ℂ) (phiW a w (us r)) /
    ((Real.sqrt 2 * pEll (typeLen a w) (us r) : ℝ) : ℂ)

end CaiFourierSparse.Learning


