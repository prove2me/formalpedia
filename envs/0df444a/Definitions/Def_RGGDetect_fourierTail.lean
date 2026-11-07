-- Prove2me | Definitions.Def_RGGDetect_fourierTail
-- name    : RGGDetect_fourierTail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:25.479829+00:00
-- url     : https://prove2.me/theorems/a9909df5-c5d2-4a2e-9e7e-42d0f56b2d55
-- title:
--   Fourier-tail weights: $w_{m,k,r}$, $B_{m,K,r}$, $F_{m,r}$ and $T_{m,r}$
-- statement:
--   Let $p\in[0,1]$.
--
--   1. (99) $w_{m,k,r}=\mathbb P\big(\mathrm{Bin}(k,1-p)+\mathrm{Bin}(m-k,p)\le r\big)$, the two binomials independent.
--   2. (100) $B_{m,K,r}=\sum_{k=K}^m\binom mk w_{m,k,r}\,\mathbb E_\rho\big[|\eta_2(\rho)|^k\big]$, where $\eta_2(z,z')$ is (4) for $z,z'$ independent uniform on $S^{d-1}$ and $p=\mathbb P\{\langle x_1,x_2\rangle\ge\tau\}$.
--   3. $F_{m,r}(u)=\sum_{k=0}^m\binom mk w_{m,k,r}u^k$ and $F^{(\ge K)}_{m,r}(u)=\sum_{k=K}^m\binom mk w_{m,k,r}u^k$, so that $B_{m,K,r}=\mathbb E_\rho[F^{(\ge K)}_{m,r}(|\eta_2(\rho)|)]$.
--   4. (101) $T_{m,r}=\{y\in\{0,1\}^m:\sum_iy_i\le r\}$.
--
--   These control the high-frequency part of the Fourier expansion of the row likelihood on the typical-degree event.
--
--   **Formalization Note** $w_{m,k,r}$ is written out as the finite binomial sum. The expectation in $B_{m,K,r}$ is the double integral of $|\eta_2(z,z')|^k$ over $z,z'$, so nothing rests on rotation invariance.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §5, eqs. (99)–(101), p.26 (PDF p.28); p.28 (PDF p.30)

import Mathlib
import Definitions.Def_RGGDetect_kappa

open MeasureTheory

namespace RGGDetect

/-- `w_{m,k,r} := P(Bin(k, 1-p) + Bin(m-k, p) ≤ r)` (99), the two binomials independent
(arXiv:2610.08517, held version, §5, p.26, eq. (99)), written out as a finite sum. -/
noncomputable def wBin (p : ℝ) (m k r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (m - k + 1),
    if i + j ≤ r then
      ((k.choose i : ℝ) * (1 - p) ^ i * p ^ (k - i)) *
        ((m - k).choose j * p ^ j * (1 - p) ^ (m - k - j))
    else 0

/-- `B_{m,K,r} := ∑_{k=K}^{m} \binom mk w_{m,k,r} E_ρ[|η₂(ρ)|^k]` (100), where the expectation is over
`z, z'` independent and uniform on `S^{d-1}` of `|η₂(z, z')|^k`, and `p = capProb d τ`
(arXiv:2610.08517, held version, §5, p.26, eq. (100)).

**Formalization Note** The paper writes `η₂(z, z')` as a function of `ρ = ⟨z, z'⟩`; the double integral
is used directly, so nothing rests on rotation invariance. -/
noncomputable def Btail (d : ℕ) (τ : ℝ) (m K r : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc K m, (m.choose k : ℝ) * wBin (capProb d τ) m k r *
    ∫ q, |eta d τ 2 ![q.1, q.2]| ^ k ∂((unifSphere d).prod (unifSphere d))

/-- The generating function `F_{m,r}(u) := ∑_{k=0}^{m} \binom mk w_{m,k,r} u^k`
(arXiv:2610.08517, held version, §5, p.28). -/
noncomputable def Fgen (p : ℝ) (m r : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * wBin p m k r * u ^ k

/-- The tail `F^{(≥K)}_{m,r}(u) := ∑_{k=K}^{m} \binom mk w_{m,k,r} u^k`
(arXiv:2610.08517, held version, §5, p.28). -/
noncomputable def FgenTail (p : ℝ) (m r K : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc K m, (m.choose k : ℝ) * wBin p m k r * u ^ k

/-- `T_{m,r} := {y ∈ {0,1}^m : ∑ y_i ≤ r}` (101) (arXiv:2610.08517, held version, §5, p.26,
eq. (101)). -/
def Tmr (m r : ℕ) : Set (Fin m → Bool) :=
  {y | (Finset.univ.filter fun i => y i = true).card ≤ r}

end RGGDetect


