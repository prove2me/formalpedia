-- Prove2me | Definitions.Def_AdvMultiplayer_Size
-- name    : AdvMultiplayer_Size
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:07.453735+00:00
-- url     : https://prove2.me/theorems/e53c19f4-e6c9-4483-9ee6-0c2a48fe7b24
-- title:
--   Instance size and the explicit constants
-- statement:
--   An instance is a triple of integers $(m,K,T)$ with $2\le m<K$ and $T\ge 1$. The module records every explicit constant of the paper as a function of the instance: $d=m-1$, $N=2Km(T+1)$, $b_N=\lceil\log_2(N+1)\rceil$, $D=2^{b_N}$, $L_{\mathrm{stab}}=\lceil\log_2(2K(T+1)N^2)\rceil$; the construction branch $T>C_bmKb_N^2$, $N\ge N_0$ with $C_b=16$, $N_0=2^{28}$; the table sizes $M=\lceil 8T^2/(mb_N)\rceil$, $B_{\mathrm{boot}}=\lceil\sqrt{T/(mK)}\rceil$, $n_{\mathrm{boot}}=\lceil T/B_{\mathrm{boot}}\rceil$, $A=\lceil T(B_{\mathrm{boot}}+b_N)/b_N\rceil$, $L_0=2^{\lceil\log_2(2b_N)\rceil}$; the quotas $q_{\mathrm{dec}}=8L_0b_N$ and $Q_{\mathrm{dec}}=B+\lceil\log_2(4dTN^2)\rceil$ with message width $B=5\lceil\log_2(TD+1)\rceil$; the launch threshold $Q$ of (51); the tuned rate $\eta$, the largest power of two with $\eta\le(1024mKL_{\mathrm{stab}})^{-1}$ and $\eta^2WT\le\mathcal J$; and the rate-dependent quantities $\beta=32\eta L_{\mathrm{stab}}$, $H=\lfloor(64\eta)^{-1}\rfloor$, $\gamma=32(K-m+1)\beta$, $h=4m\eta$, $B_{\mathrm{cap}}=1/(32\eta)$.
--
--   These numbers are shared by every definition and theorem of the mission.
--
--   **Formalization Note.** Ceilings of logarithms use `Nat.clog`. Quantities depending on a rate take the rate as an argument, since Section 3 holds for every admissible dyadic rate.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 1.1 p.3; Sections 3, 4, 6, 7; App. B.10

import Mathlib

namespace AdvMultiplayer

/-- **Instance size.** Gan, *Square-Root Regret for Adversarial Multiplayer Bandits without
Collision Information or Shared Randomness*, arXiv:2610.05688, Section 1.1, p.3: integers
`2 ≤ m < K` and `T ≥ 1`.

The namespace `Size` below holds every explicit constant of the paper as a function of
`(m, K, T)`: Section 3 (p.13, p.15), Section 4 (pp.21, 27, 32), Section 6 (pp.41–42), Section 7
(p.45), Section 5.6 (p.39), Appendix B.10.

**Formalization Note.** Ceilings of ratios of naturals are `cdiv`; `⌈log₂ n⌉` is `Nat.clog 2 n`
(not `Nat.log2`, which floors). `K - m + 1` and `m - 1` are natural subtractions and exact because
`2 ≤ m < K`. Quantities that depend on a learning rate take the rate `η` as an argument, because
Section 3 holds for every admissible dyadic rate; `eta` is the tuned rate of Section 7. -/
structure Size where
  /-- Number of players. -/
  m : ℕ
  /-- Number of arms. -/
  K : ℕ
  /-- Horizon. -/
  T : ℕ
  two_le_m : 2 ≤ m
  m_lt_K : m < K
  one_le_T : 1 ≤ T

namespace Size

variable (p : Size)

/-- `⌈a / b⌉` for naturals. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `d = m - 1`, the number of followers (p.6). -/
def d : ℕ := p.m - 1

/-- `N = 2Km(T+1)` (p.4). -/
def N : ℕ := 2 * p.K * p.m * (p.T + 1)

/-- `b_N = ⌈log₂(N+1)⌉` (p.4). -/
def bN : ℕ := Nat.clog 2 (p.N + 1)

/-- `D = 2^{b_N}` (p.6). -/
def D : ℕ := 2 ^ p.bN

/-- `L_stab = ⌈log₂(2K(T+1)N²)⌉` (p.13). -/
def Lstab : ℕ := Nat.clog 2 (2 * p.K * (p.T + 1) * p.N ^ 2)

/-- `C_b = 16` (p.41). -/
def Cb : ℕ := 16

/-- `N₀ = 2²⁸` (p.41). -/
def N0 : ℕ := 2 ^ 28

/-- The construction branch (45), p.41: `T > C_b m K b_N²` and `N ≥ N₀`. -/
def branch : Prop := Cb * p.m * p.K * p.bN ^ 2 < p.T ∧ N0 ≤ p.N

instance : Decidable p.branch := by unfold branch; infer_instance

/-- `M = ⌈8T²/(m b_N)⌉`, the number of rows (p.41). -/
def M : ℕ := cdiv (8 * p.T ^ 2) (p.m * p.bN)

/-- `B_boot = ⌈√(T/(mK))⌉` (46), p.41. -/
noncomputable def Bboot : ℕ := ⌈Real.sqrt ((p.T : ℝ) / ((p.m : ℝ) * (p.K : ℝ)))⌉₊

/-- `n_boot = ⌈T/B_boot⌉` (46), p.41. -/
noncomputable def nboot : ℕ := cdiv p.T p.Bboot

/-- `A = ⌈T(B_boot + b_N)/b_N⌉` (47), p.41. -/
noncomputable def A : ℕ := cdiv (p.T * (p.Bboot + p.bN)) p.bN

/-- `L₀ = 2^{⌈log₂(2b_N)⌉}` (47), p.41. -/
def L0 : ℕ := 2 ^ Nat.clog 2 (2 * p.bN)

/-- `q_dec = 8 L₀ b_N`, the bootstrap decoding quota (p.41). -/
def qdec : ℕ := 8 * p.L0 * p.bN

/-- `C_h = 4096` (p.42). -/
def Ch : ℕ := 4096

/-- `h_boot = ⌈C_h L₀ b_N⌉` (p.42). The argument is an integer. -/
def hboot : ℕ := Ch * p.L0 * p.bN

/-- `C_* = 2²⁰` (p.42). -/
def Cstar : ℕ := 2 ^ 20

/-- The launch threshold `Q` of (51), p.42. The argument of the ceiling is an integer. -/
noncomputable def Qlaunch : ℕ :=
  Cstar * (p.m ^ 2 * p.K * p.Bboot * p.bN + p.m * p.hboot * p.nboot + p.m ^ 2 * p.hboot * p.bN
    + p.m * p.Bboot)

/-- `C₁ = 2²⁰` (p.45). -/
def C1 : ℕ := 2 ^ 20

/-- `𝒥 = ⌈log₂(C(K,m)+1)⌉ + m` (p.45). -/
def Jtune : ℕ := Nat.clog 2 (p.K.choose p.m + 1) + p.m

/-- `W = C₁ m² K b_N` (p.45). -/
def Wtune : ℕ := C1 * p.m ^ 2 * p.K * p.bN

/-- The exponent of the tuned rate: the least `e` such that `2^{-e}` satisfies the two
constraints of p.45. The set is nonempty for every instance, because `2^{-e} → 0`. -/
noncomputable def etaExp : ℕ :=
  sInf {e : ℕ | ((1 : ℝ) / 2) ^ e ≤ ((1024 : ℝ) * p.m * p.K * p.Lstab)⁻¹ ∧
    (((1 : ℝ) / 2) ^ e) ^ 2 * p.Wtune * p.T ≤ p.Jtune}

/-- The tuned learning rate of p.45: the largest power of two `η` with
`η ≤ (1024 m K L_stab)⁻¹` and `η² W T ≤ 𝒥`. Every admissible value is below one, so a negative
exponent is never needed. -/
noncomputable def eta : ℝ := ((1 : ℝ) / 2) ^ p.etaExp

/-- `β = 32 η L_stab` (p.13), for a rate `η`. -/
noncomputable def betaOf (η : ℝ) : ℝ := 32 * η * p.Lstab

/-- `H = ⌊(64η)⁻¹⌋` (p.13), for a rate `η`. -/
noncomputable def gridOf (η : ℝ) : ℕ := ⌊(64 * η)⁻¹⌋₊

/-- `γ = 32(K-m+1)β` (7), p.14, for a rate `η`. -/
noncomputable def gammaOf (η : ℝ) : ℝ := 32 * ((p.K - p.m + 1 : ℕ) : ℝ) * p.betaOf η

/-- The proposal probability `h = 4mη` (p.15), for a rate `η`. -/
noncomputable def propOf (η : ℝ) : ℝ := 4 * p.m * η

/-- `B_cap = 1/(32η)` (p.15), for a rate `η`. -/
noncomputable def BcapOf (η : ℝ) : ℝ := 1 / (32 * η)

/-- The service cap `4ηD` of (11), p.14, as a natural number (it is an integer because `ηD` is). -/
noncomputable def capOf (η : ℝ) : ℕ := ⌊4 * η * p.D⌋₊

/-- `R = 64 m²(2K-m)` (8), p.14. -/
def Rconst : ℕ := 64 * p.m ^ 2 * (2 * p.K - p.m)

/-- Field width `L = ⌈log₂(TD+1)⌉` (p.32). -/
def Lfield : ℕ := Nat.clog 2 (p.T * p.D + 1)

/-- Message width `B = 5L` (pp.21, 32). -/
def Bmsg : ℕ := 5 * p.Lfield

/-- `Q_dec = B + ⌈log₂(4dTN²)⌉` (20), p.21. -/
def Qdec : ℕ := p.Bmsg + Nat.clog 2 (4 * p.d * p.T * p.N ^ 2)

/-- `ζ = (1-1/K)^d` (p.27). -/
noncomputable def zeta : ℝ := (1 - 1 / (p.K : ℝ)) ^ p.d

/-- The next clipped grid boundary `τ̄(σ) = min{T+1, H(⌊σ/H⌋+1)}` (pp.13, 29), for a grid `H`. -/
def gridEnd (H σ : ℕ) : ℕ := min (p.T + 1) (H * (σ / H + 1))

/-- `Q_boot = m^{3/2} √(KT) b_N²` (52), p.44. -/
noncomputable def Qboot : ℝ :=
  (p.m : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((p.K : ℝ) * p.T) * (p.bN : ℝ) ^ 2

/-- `Δ_boot = 5N⁻²` (53), p.44. -/
noncomputable def Dboot : ℝ := 5 / (p.N : ℝ) ^ 2

/-- The phase bounds and their sum `C_tr` (40), p.39. -/
noncomputable def Ctr : ℝ :=
  8 * p.d * p.K / (1 - Real.exp (-1)) * (4 * p.Qdec + Real.log p.d)
    + 8 * p.d * p.K / (1 - Real.exp (-1)) * (2 * p.Qdec + Real.log p.d + 1)
    + (2 * p.d * p.K + 12 * p.d * p.K / (1 - Real.exp (-1)) * (Real.log p.d + 1))

end Size

end AdvMultiplayer


