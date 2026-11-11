-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Counting
-- name    : RSBeyondJohnson_FirstOrder_Counting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:08.727194+00:00
-- url     : https://prove2.me/theorems/0966d822-b3cc-4307-942a-7dc4d5a45234
-- title:
--   Incidence factor $\Pi_r$ (31), $\Psi_D$ and $E^{(\ell)}_{\mathrm{ord}}$ (33)–(34), and the counting parameters (43)
-- statement:
--   For $r\ge0$ and $k\le T\le n$, the **incidence factor** is $\Pi_r(T)=\prod_{i=1}^r\frac{n-k+i}{T-k+i}$ (empty product $1$).
--   For $D\ge1$, $n\ge A>D$, $B\ge1$, $H\ge0$, $\ell\ge1$, $D+1\le L\le A$:
--   $$\Psi_D(B)=1+(2D-1)(2B-1)+2(B-2D-1)_+,$$
--   $$E^{(\ell)}_{\mathrm{ord}}(D,A,n;B,H;L)=(2B-1)H+\frac{n-L+1}{A-L+1}\big(\ell B+H\Psi_D(B)\big)+\ell(n-L)B,$$
--   and omitting $L$ means $L=D+1$.
--   The first-order counting parameters (43): $\lambda_{\mathrm{agr}}=(n-D)/(A-D)$, $\tau=\max\{0,2D-3\}$, $u=1+\tau(B-1)$, $v=\min\{u,\tau(M-1)+D\}$, $F_{\mathrm{reg}}=Bv+M(u-v)$, $S=\max\{B,(2M-1)B-M^2\}$, $H_s=(2M-1)H$, and $J_\ell=H(2uv-v^2)+2(\ell+\tau H)F_{\mathrm{reg}}$.
--
--   **Formalization Note.** $\Pi_r$, $\Psi_D$, $E_{\mathrm{ord}}$ and $\lambda_{\mathrm{agr}}$ are real-valued (the degree arguments of $\Psi_D$, $E_{\mathrm{ord}}$ are real so that the integers $S,H_s$ can be passed); $\tau,u,v,F_{\mathrm{reg}},S,H_s,J_\ell$ are integers. They are only used in the stated ranges, where no denominator vanishes.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 26, (31); p. 28, (33)–(34); p. 33, (43)

import Mathlib

open Finset

namespace RSBeyondJohnson.FirstOrder

/-!
# Counting functions: the incidence factor `Π_r` (31), `Ψ_D` and `E^(ℓ)_ord` (33)–(34), and the
first-order counting parameters (43)

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson*, STOC 2027 submission (manuscript of
November 2, 2026), §4.1, p. 26, (31); §4.2, p. 28, (33)–(34); §5.3, p. 33, (43).

All counts are real numbers; the degree arguments `B`, `H` of `Ψ_D` and `E_ord` are real so
that the integer bounds `S`, `H_s` of (43) can be passed directly; `(x)_+` is `max 0 x`. They are
used only in the ranges the paper states (`k ≤ T ≤ n` for `Π_r`; `D ≥ 1`, `n ≥ A > D`, `B ≥ 1`,
`D + 1 ≤ L ≤ A` for `E_ord`; `1 ≤ D`, `1 ≤ M ≤ B` for (43)), where no denominator vanishes.
-/

/-- The incidence factor `Π_r(T) = ∏_{i=1}^{r} (n − k + i)/(T − k + i)` ((31), p. 26; an empty
product when `r = 0`). -/
noncomputable def incidenceFactor (n k r T : ℕ) : ℝ :=
  ∏ i ∈ Icc 1 r, (((n : ℝ) - k + i) / ((T : ℝ) - k + i))

/-- `Ψ_D(B) = 1 + (2D − 1)(2B − 1) + 2(B − 2D − 1)_+` ((33), p. 28). -/
noncomputable def psiD (D : ℕ) (B : ℝ) : ℝ :=
  1 + (2 * (D : ℝ) - 1) * (2 * B - 1) + 2 * max 0 (B - 2 * D - 1)

/-- `E^(ℓ)_ord(D, A, n; B, H; L) = (2B − 1)H + ((n − L + 1)/(A − L + 1))(ℓB + HΨ_D(B))
+ ℓ(n − L)B` ((33), p. 28). Omitting `L` means `L = D + 1` ((34)). -/
noncomputable def eOrd (ℓ D A n : ℕ) (B H : ℝ) (L : ℕ) : ℝ :=
  (2 * B - 1) * H + ((n : ℝ) - L + 1) / ((A : ℝ) - L + 1) * (ℓ * B + H * psiD D B) +
    ℓ * ((n : ℝ) - L) * B

/-- `λ_agr = (n − D)/(A − D)` ((43), p. 33; also Theorems 5.1, 5.2). -/
noncomputable def lamAgr (n D A : ℕ) : ℝ := ((n : ℝ) - D) / ((A : ℝ) - D)

/-- `τ = max{0, 2D − 3}` ((43)). -/
def tauD (D : ℕ) : ℤ := max 0 (2 * (D : ℤ) - 3)

/-- `u = 1 + τ(B − 1)` ((43)). -/
def uReg (D B : ℕ) : ℤ := 1 + tauD D * ((B : ℤ) - 1)

/-- `v = min{u, τ(M − 1) + D}` ((43)). -/
def vReg (D B M : ℕ) : ℤ := min (uReg D B) (tauD D * ((M : ℤ) - 1) + D)

/-- `F_reg = B v + M(u − v)` ((43)). -/
def fReg (D B M : ℕ) : ℤ := (B : ℤ) * vReg D B M + M * (uReg D B - vReg D B M)

/-- `S = max{B, (2M − 1)B − M²}` ((43)). -/
def sOrd (B M : ℕ) : ℤ := max (B : ℤ) ((2 * (M : ℤ) - 1) * B - (M : ℤ) ^ 2)

/-- `H_s = (2M − 1)H` ((43)). -/
def hOrd (M H : ℕ) : ℤ := (2 * (M : ℤ) - 1) * H

/-- `J_ℓ = H(2uv − v²) + 2(ℓ + τH) F_reg` (p. 33). -/
def jReg (ℓ D B M H : ℕ) : ℤ :=
  (H : ℤ) * (2 * uReg D B * vReg D B M - vReg D B M ^ 2) + 2 * ((ℓ : ℤ) + tauD D * H) * fReg D B M

end RSBeyondJohnson.FirstOrder


