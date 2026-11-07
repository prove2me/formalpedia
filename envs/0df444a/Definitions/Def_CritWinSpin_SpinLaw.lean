-- Prove2me | Definitions.Def_CritWinSpin_SpinLaw
-- name    : CritWinSpin_SpinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:03.581862+00:00
-- url     : https://prove2.me/theorems/dcaf04ba-4de8-475a-a9d6-4b0f46ad6524
-- title:
--   Single-site spin law $\rho$ on $A\subset[-1,1]\cap\mathbb Q$, $\phi$, $I$, $\tau$, GHS and type $p$
-- statement:
--   A **single-site spin law** consists of a finite set $A\subset[-1,1]\cap\mathbb Q$ with $\pm1\in A$ and $A=-A$, and a rational probability $\rho$ on $A$ with $\rho(x)=\rho(-x)>0$. Write $v=\mathrm{Var}_\rho(X)=\sum_{x\in A}x^2\rho(x)$ and $\tau=1/v$. The cumulant generating function and its Legendre–Fenchel transform are
--   $$\phi(t)=\log\sum_{x\in A}\rho(x)e^{tx},\qquad I(m)=\sup_{t\in\mathbb R}\{tm-\phi(t)\}.$$
--   The tilted law is $\rho_t(x)=\rho(x)e^{tx-\phi(t)}$. The law satisfies the **single-site GHS inequality** if $\phi^{(3)}(t)\le0$ for all $t\ge0$. It has **type $p$** if $p\ge2$, $\phi^{(2j)}(0)=0$ for $2\le j<p$, and $\phi^{(2p)}(0)<0$; the critical exponent is $d_p=(p-1)/p$. For $\theta$ real, $F_\theta(m)=\frac{\tau+\theta}{2}m^2-I(m)$ is the single-spin free energy, and $\kappa=-\phi^{(2p)}(0)/[(2p)!\,v^{2p}]$ is the coefficient in the expansion of $I$.
--
--   These are the standing objects of the whole paper. The general finite symmetric rational alphabet of the abstract reduces to this normalisation by rescaling.
--
--   **Formalization Note** The weight $\rho$ is a function on $\mathbb Q$ of which only the values on $A$ are used. Odd cumulants vanish by symmetry, so they are not part of the definition of type $p$.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §2.1, p.9, eq. (5); Definition 2.1, p.9; Lemma 3.1(i), p.11; eq. (10), p.10

import Mathlib
set_option autoImplicit false

namespace CritWinSpin

/-- A **single-site spin law** in the normalisation of §2.1 (printed p.9): a finite set
`A ⊂ [−1, 1] ∩ ℚ` with `±1 ∈ A` and `A = −A`, and a rational probability `ρ : A → ℚ_{>0}` with
`ρ(x) = ρ(−x) > 0` for every `x ∈ A`.

Source: S. Liu, B. Zhang, K. Ren, *The Critical Window for Sampling and Learning-to-Sample in Spin
Systems*, STOC 2027 submission (manuscript sha256 f77584da…), §2.1, p.9.

**Formalization Note.** `ρ` is a function `ℚ → ℚ`; only its values on `A` are ever used. The
abstract's general finite symmetric `A ⊂ ℚ` is reduced to this normalisation by the rescaling the
paper describes on p.9; every theorem of the paper is stated under the §2.1 normalisation. -/
structure SpinLaw where
  /-- The spin alphabet `A`. -/
  A : Finset ℚ
  /-- The single-site weights `ρ(x)`. -/
  ρ : ℚ → ℚ
  /-- `A ⊂ [−1, 1]`. -/
  mem_Icc : ∀ x ∈ A, -1 ≤ x ∧ x ≤ 1
  /-- `1 ∈ A`. -/
  one_mem : (1 : ℚ) ∈ A
  /-- `−1 ∈ A`. -/
  neg_one_mem : (-1 : ℚ) ∈ A
  /-- `A = −A`. -/
  neg_mem : ∀ x ∈ A, -x ∈ A
  /-- `ρ(x) > 0` on `A`. -/
  pos : ∀ x ∈ A, 0 < ρ x
  /-- `ρ(−x) = ρ(x)` on `A`. -/
  symm : ∀ x ∈ A, ρ (-x) = ρ x
  /-- `∑_{x∈A} ρ(x) = 1`. -/
  sum_one : ∑ x ∈ A, ρ x = 1

/-- The variance `v = Var_ρ(X) = ∑_{x∈A} x² ρ(x)` (a rational number; §2.1, p.9). -/
def varQ (S : SpinLaw) : ℚ := ∑ x ∈ S.A, x ^ 2 * S.ρ x

/-- The critical threshold `τ = 1/v` as a rational number (§2.1, p.9). -/
def tauQ (S : SpinLaw) : ℚ := 1 / varQ S

/-- The variance `v` as a real number. -/
noncomputable def variance (S : SpinLaw) : ℝ := (varQ S : ℝ)

/-- The critical threshold `τ = (Var_ρ X)^{-1}` as a real number (§2.1, p.9). -/
noncomputable def tau (S : SpinLaw) : ℝ := ((tauQ S : ℚ) : ℝ)

/-- The cumulant generating function `ϕ(t) = log ∑_{x∈A} ρ(x) e^{tx}`, eq. (5), p.9. -/
noncomputable def phi (S : SpinLaw) (t : ℝ) : ℝ :=
  Real.log (∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ)))

/-- The tilted law `ρ_t(x) = ρ(x) e^{tx − ϕ(t)}` (Definition 2.1, p.9). -/
noncomputable def tilt (S : SpinLaw) (t : ℝ) (x : ℚ) : ℝ :=
  (S.ρ x : ℝ) * Real.exp (t * (x : ℝ) - phi S t)

/-- The Cramér rate function `I(m) = sup_{t∈ℝ} {tm − ϕ(t)}`, eq. (5), p.9.

**Formalization Note.** The paper defines `I` on `m ∈ [−1, 1]`; there the supremum is finite
(since `ϕ(t) ≥ |t| + log ρ(±1)`), so the real `⨆` is the true supremum. Every statement of the
mission uses `rateI` only for `m ∈ [−1, 1]`. -/
noncomputable def rateI (S : SpinLaw) (m : ℝ) : ℝ := ⨆ t : ℝ, (t * m - phi S t)

/-- **Definition 2.1 (p.9), single-site GHS condition:** `ϕ'''(t) ≤ 0` for all `t ≥ 0`. -/
def IsGHS (S : SpinLaw) : Prop := ∀ t : ℝ, 0 ≤ t → iteratedDeriv 3 (phi S) t ≤ 0

/-- **Type `p`** (Lemma 3.1(i), p.11; eq. (1), p.2): `p ≥ 2`, the cumulants
`κ_4, …, κ_{2p−2}` vanish and `κ_{2p} = ϕ^{(2p)}(0) < 0`. The `j`-th cumulant is `ϕ^{(j)}(0)`.

**Formalization Note.** Odd cumulants vanish by the symmetry of `ρ`, so they are not listed. -/
def IsTypeP (S : SpinLaw) (p : ℕ) : Prop :=
  2 ≤ p ∧ (∀ j : ℕ, 2 ≤ j → j < p → iteratedDeriv (2 * j) (phi S) 0 = 0) ∧
    iteratedDeriv (2 * p) (phi S) 0 < 0

/-- The critical exponent `d_p = (p − 1)/p` (p.2). -/
noncomputable def dExp (p : ℕ) : ℝ := ((p : ℝ) - 1) / p

/-- The constant `κ = −κ_{2p} / [(2p)! v^{2p}]` of the expansion (1) (Lemma 3.1(i), p.11). -/
noncomputable def kappa (S : SpinLaw) (p : ℕ) : ℝ :=
  -iteratedDeriv (2 * p) (phi S) 0 / (((2 * p).factorial : ℝ) * variance S ^ (2 * p))

/-- The single-spin free energy `F_θ(m) = (β/2) m² − I(m)` with `β = τ + θ`, eq. (10), p.10. -/
noncomputable def Ftheta (S : SpinLaw) (θ m : ℝ) : ℝ := ((tau S + θ) / 2) * m ^ 2 - rateI S m

end CritWinSpin


