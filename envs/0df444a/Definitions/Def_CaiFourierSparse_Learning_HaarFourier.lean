-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_HaarFourier
-- name    : CaiFourierSparse_Learning_HaarFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:12:02.150297+00:00
-- url     : https://prove2.me/theorems/7b2ae7b1-b198-4cf8-96f2-d456a53a26ce
-- title:
--   The Haar–Fourier basis, the projection $P_N$, the endpoint correction $\iota^\perp$, $D_k$ and $\|\mathrm{bottom}_s\|_2^2$
-- statement:
--   Let $K=2^a$ and $N=2^b$ (in the paper $K\ge k$, $N\ge2F$, $K\mid 2N$). The frequencies $\{-N,\dots,N-1\}$ are cut into the $2N/K$ blocks $b_i+[K]$, $b_i=-N+Ki$, $[n]=\{0,\dots,n-1\}$. In each block the Haar basis consists of the **scaling vector** $H^{sc}=\mathbf 1_{[K]}/\sqrt K$ and the **wavelets** $H^{wav}_{s+[\ell]}=(\mathbf 1_{s+[\ell/2]}-\mathbf 1_{s+\ell/2+[\ell/2]})/\sqrt\ell$ for every power of two $\ell=2^m\in[2,K]$ and $s\in\{0,\ell,\dots,K-\ell\}$, shifted to the block. `HaarIdx` records (block, type, position), `haarIdxSet b a` is the index set of $\mathcal H_{2N}$, `haarVec` the vector $H$ on $\mathbb Z$ and `haarSupp` its support size $|H|$ ($K$ or $\ell$). The **Haar–Fourier function** of $H$ is
--   $$\varphi_H(t)=\frac1{\sqrt2}\sum_{n=-N}^{N-1}H(n)(-1)^ne^{i\pi nt}\qquad\text{(eq. (13), `phiH`)},$$
--   and $\alpha_H=\langle x,\varphi_H\rangle_{[-1,1]}$ (`hfCoeff`). The projection onto $\operatorname{span}(\mathcal B)$ is $P_Nz=\sum_{n=-N}^{N-1}\hat z[n]e^{i\pi nt}/\sqrt2$, eq. (15) (`projN`). With $\iota(t)=t$, $\iota^\perp=\iota-P_N\iota$ (`iotaPerp`), $c_x=(x(1)-x(-1))/2$ (`endCoeff`) and $g_N=P_Nx+c_x\iota^\perp$ (`gN`). The weighted density of eq. (1) is $D_k(t)=1/\big((2+4\ln k)\max\{1-|t|,k^{-2}\}\big)$ (`Dk`). For a vector $v$ on a finite index set $T$, $\|\mathrm{bottom}_s(v)\|_2^2$ is the squared norm left after erasing the $s$ largest entries in absolute value, i.e. $\min_{S\subseteq T,|S|\le s}\sum_{i\in T\setminus S}|v_i|^2$ (`bottomSq`); it does not depend on how ties are broken.
--
--   **Formalization Note.** $P_N$ is defined by the Fourier sum (15), which Fact 4.2 shows equals the orthogonal projection onto $\mathcal B$; $(-1)^n$ is written $(-1)^{|n|}$.
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Definition 4.1, eqs. (1), (13)–(15), Theorem 4.3 and §2, printed pp. 3, 6, 12–13 (PDF pp. 5, 8, 14–15)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal

namespace CaiFourierSparse.Learning

open MeasureTheory Complex

/-! # The Haar–Fourier basis, the projection `P_N`, the endpoint correction, `D_k` and
`bottom_s` (Cai–Chen–Shao–Wang, Definition 4.1, eqs. (1), (12)–(15), Theorem 4.3, §2)

`K = 2^a` and `N = 2^b` are powers of two (`K ≥ k`, `N ≥ 2F`, `K ∣ 2N`, i.e. `a ≤ b + 1`). The
low frequencies `{-N, …, N-1}` are cut into the `2N/K` blocks `b_i + [K]`, `b_i = -N + K i`.
In each block the Haar basis `H_K` consists of the scaling vector `H^sc = 1_{[K]}/√K` and the
wavelets `H^wav_{s+[ℓ]} = (1_{s+[ℓ/2]} - 1_{s+ℓ/2+[ℓ/2]})/√ℓ` for every power of two
`ℓ = 2^m ∈ [2, K]` and every `s ∈ {0, ℓ, …, K - ℓ}`. The Haar–Fourier function of a Haar vector
`H` is `φ_H(t) = (1/√2) ∑_n H(n) (-1)^n e^{iπ n t}` (eq. (13)). -/

/-- An index of a vector of the Haar basis `H_{2N}`: the block `blk` (block `b_blk + [K]`), the
type (`none` = scaling vector, `some m` = wavelet of support `ℓ = 2^m`), and the position `pos`
of a wavelet inside the block (`s = ℓ · pos`; `pos = 0` for the scaling vector). -/
structure HaarIdx where
  blk : ℕ
  lev : Option ℕ
  pos : ℕ
  deriving DecidableEq

/-- The finite set of indices of `H_{2N}` for `N = 2^b`, `K = 2^a`. -/
def haarIdxSet (b a : ℕ) : Finset HaarIdx :=
  (Finset.range (2 * 2 ^ b / 2 ^ a)).biUnion fun i =>
    insert (⟨i, none, 0⟩ : HaarIdx)
      ((Finset.Icc 1 a).biUnion fun m =>
        (Finset.range (2 ^ a / 2 ^ m)).image fun p => (⟨i, some m, p⟩ : HaarIdx))

/-- Support size `|H|` of a Haar vector: `K` for the scaling vector, `ℓ = 2^m` for a wavelet. -/
def haarSupp (a : ℕ) (H : HaarIdx) : ℕ :=
  match H.lev with
  | none => 2 ^ a
  | some m => 2 ^ m

/-- The Haar vector `H ∈ H_{2N}` as a function on `ℤ` (`N = 2^b`, `K = 2^a`). -/
noncomputable def haarVec (b a : ℕ) (H : HaarIdx) (n : ℤ) : ℝ :=
  let base : ℤ := -(2 ^ b : ℤ) + (2 ^ a : ℤ) * H.blk
  match H.lev with
  | none => if base ≤ n ∧ n < base + 2 ^ a then 1 / Real.sqrt ((2 : ℝ) ^ a) else 0
  | some m =>
    let ℓ : ℤ := 2 ^ m
    let s : ℤ := base + ℓ * H.pos
    if s ≤ n ∧ n < s + ℓ / 2 then 1 / Real.sqrt ((2 : ℝ) ^ m)
    else if s + ℓ / 2 ≤ n ∧ n < s + ℓ then -1 / Real.sqrt ((2 : ℝ) ^ m) else 0

/-- The Haar–Fourier function `φ_H(t) = (1/√2) ∑_{n=-N}^{N-1} H(n) (-1)^n e^{iπ n t}` (eq. (13)). -/
noncomputable def phiH (b a : ℕ) (H : HaarIdx) (t : ℝ) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) * ∑ n ∈ Finset.Ico (-(2 ^ b : ℤ)) (2 ^ b),
    (haarVec b a H n : ℂ) * (-1 : ℂ) ^ n.natAbs *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))

/-- The Haar–Fourier coefficient `α_H = ⟨x, φ_H⟩_{[-1,1]}`. -/
noncomputable def hfCoeff (b a : ℕ) (x : ℝ → ℂ) (H : HaarIdx) : ℂ := winner x (phiH b a H)

/-- The projection `P_N z = ∑_{n=-N}^{N-1} ẑ[n] e^{iπ n t}/√2` onto `span(B)` (eq. (15)). -/
noncomputable def projN (N : ℕ) (z : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico (-(N : ℤ)) N, fsc z n *
    Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) * ((Real.sqrt 2)⁻¹ : ℂ)

/-- `ι(t) = t`. -/
def iota (t : ℝ) : ℂ := (t : ℂ)

/-- `ι⊥ = ι - P_N ι`, the component of `ι` orthogonal to `span(B)`. -/
noncomputable def iotaPerp (N : ℕ) (t : ℝ) : ℂ := iota t - projN N iota t

/-- The endpoint coefficient `c_x = (x(1) - x(-1))/2`. -/
noncomputable def endCoeff (x : ℝ → ℂ) : ℂ := (x 1 - x (-1)) / 2

/-- `g_N = P_N x + c_x · ι⊥`, the approximation of `x` in `span(B ∪ {ι})`. -/
noncomputable def gN (N : ℕ) (x : ℝ → ℂ) (t : ℝ) : ℂ :=
  projN N x t + endCoeff x * iotaPerp N t

/-- The weighted sampling density `D_k(t) = 1 / ((2 + 4 ln k) · max{1 - |t|, k^{-2}})`, eq. (1). -/
noncomputable def Dk (k : ℕ) (t : ℝ) : ℝ :=
  1 / ((2 + 4 * Real.log k) * max (1 - |t|) ((k : ℝ) ^ 2)⁻¹)

/-- `‖bottom_s(v)‖²₂` for a vector `v` indexed by a finite set `T`: the squared norm left after
erasing the `s` largest entries in absolute value. It is the minimum over sets `S ⊆ T` with
`|S| ≤ s` of `∑_{i ∈ T \ S} |v_i|²`, hence independent of how ties are broken. -/
noncomputable def bottomSq {ι : Type*} [DecidableEq ι] (v : ι → ℂ) (T : Finset ι) (s : ℕ) : ℝ :=
  ((T.powerset.filter (fun S => S.card ≤ s)).image
    (fun S => ∑ i ∈ T \ S, ‖v i‖ ^ 2)).min' (by
      refine ⟨∑ i ∈ T \ ∅, ‖v i‖ ^ 2, Finset.mem_image.mpr ⟨∅, ?_, rfl⟩⟩
      simp)

end CaiFourierSparse.Learning


