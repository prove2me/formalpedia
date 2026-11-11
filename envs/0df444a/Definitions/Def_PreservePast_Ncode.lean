-- Prove2me | Definitions.Def_PreservePast_Ncode
-- name    : PreservePast_Ncode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:48.913844+00:00
-- url     : https://prove2.me/theorems/6feae5d1-5358-44d8-8caa-c4f66d082bcf
-- title:
--   Code length $N_p(a_0,b_0,L,\delta)$ of the multiscale nuclear-ball code
-- statement:
--   Let $a_0,b_0\ge0$, $k=\min(a_0,b_0)$, $L\ge0$, $\delta>0$ and $p\in\{1,2\}$. Put $N_p(a_0,b_0,L,\delta)=0$ if $\delta\ge L$. If $0<\delta<L$, put
--   $$
--   h=\min\{k,\lceil(4L/\delta)^p\rceil\},\quad J=\lfloor\log_2h\rfloor,\quad r_j=\min\{2^j,h-2^j+1\},\quad S_j=L2^{-j/p},\quad \eta_j=\tfrac\delta8 2^{-(J-j)/2}
--   $$
--   for $0\le j\le J$, and
--   $$
--   N_p(a_0,b_0,L,\delta)=\Big\lceil(a_0+b_0+1)\sum_{j=0}^{J}r_j\log_2(1+6S_j/\eta_j)\Big\rceil .
--   $$
--   For $z=L/\delta>1$ the comparison function is $E_p(k,z)=z^p$ if $1<z\le k^{1/p}$ and $E_p(k,z)=k\log_2(2+z/k^{1/p})$ if $z>k^{1/p}$. The reconstruction error of the code is measured in the operator norm for $p=1$ and in the Frobenius norm for $p=2$.
--
--   These are the bit counts of Lemma 4 and of Theorem 9.
--
--   **Formalization Note** $r_j$ is computed in the integers (no truncated subtraction), $J$ is `Nat.log 2 h`; the operator norm is the published `WainwrightHDS.NucNorm.opNorm2` and the Frobenius norm the published `LowRankMEG.frobNorm`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19), Lemma 4, (41)–(42)

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace PreservePast

/-- **The multiscale code length** `N_p(a₀, b₀, L, δ)` of Lemma 4.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.1, p.17 (PDF p.19), Lemma 4 and (41): "N_p = 0 if δ ≥ L. If 0 < δ < L, put
h = min{k, ⌈(4L/δ)^p⌉}, J = ⌊log₂ h⌋, r_j = min{2^j, h − 2^j + 1}, S_j = L2^{−j/p},
η_j = (δ/8)2^{−(J−j)/2} (0 ≤ j ≤ J). One may take
N_p(a₀, b₀, L, δ) = ⌈(a₀ + b₀ + 1) Σ_{j=0}^{J} r_j log₂(1 + 6S_j/η_j)⌉", with `k = min(a₀, b₀)`.

**Formalization Note.** `⌈·⌉` is `Nat.ceil` and `J = ⌊log₂ h⌋` is `Nat.log 2 h`; `r_j` is computed
in `ℤ` (no truncated subtraction), and the logarithm and the powers `2^{−j/p}`, `2^{−(J−j)/2}` in `ℝ`.
The definition is used for `p ∈ {1, 2}`. -/
noncomputable def Ncode (p a₀ b₀ : ℕ) (L δ : ℝ) : ℕ :=
  if L ≤ δ then 0 else
    let h : ℕ := min (min a₀ b₀) ⌈(4 * L / δ) ^ p⌉₊
    let J : ℕ := Nat.log 2 h
    ⌈((a₀ + b₀ + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (J + 1),
        ((min ((2 : ℤ) ^ j) ((h : ℤ) - 2 ^ j + 1) : ℤ) : ℝ) *
          Real.logb 2 (1 + 6 * (L * (2 : ℝ) ^ (-(j : ℝ) / p)) /
            (δ / 8 * (2 : ℝ) ^ (-((J : ℝ) - j) / 2)))⌉₊

/-- The comparison function `E_p(k, z)` of Lemma 4 (p.17), for `z = L/δ > 1`:
`E_p(k, z) = z^p` if `1 < z ≤ k^{1/p}`, and `k log₂(2 + z/k^{1/p})` if `z > k^{1/p}`. -/
noncomputable def Ecode (p k : ℕ) (z : ℝ) : ℝ :=
  if z ≤ (k : ℝ) ^ (1 / (p : ℝ)) then z ^ p else k * Real.logb 2 (2 + z / (k : ℝ) ^ (1 / (p : ℝ)))

/-- The reconstruction error of Lemma 4 (p.17): "For p = 1 measure reconstruction error in operator
norm, and for p = 2 measure it in Frobenius norm." `codeErr 1` is the ℓ₂ operator norm and
`codeErr p` for `p ≠ 1` the Frobenius norm (used for `p = 2`). -/
noncomputable def codeErr {a b : ℕ} (p : ℕ) (A : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  if p = 1 then WainwrightHDS.NucNorm.opNorm2 A else LowRankMEG.frobNorm A

end PreservePast


