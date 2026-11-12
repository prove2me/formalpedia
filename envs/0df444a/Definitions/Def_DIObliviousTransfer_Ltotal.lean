-- Prove2me | Definitions.Def_DIObliviousTransfer_Ltotal
-- name    : DIObliviousTransfer_Ltotal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:05:54.270446+00:00
-- url     : https://prove2.me/theorems/7c514120-82d5-41f3-b79d-3586cd3c6ae1
-- title:
--   The common schedule (7)–(9) and the complete-OT sizes (26)
-- statement:
--   Fix $k=6$, $a_*=0.047$, $\delta_*=1/2$, an integer $N_0$ and a loss threshold $\eta_{\mathrm{MS}}$. For security parameter $\lambda$, leakage budget $\ell$ and capacity $q$, the schedule (7) is
--   $$m=\mathrm{Next}(\max\{100q,100\ell,s_\lambda\}),\quad n=kN_0m,\quad t_A=\lceil m/200\rceil,\quad L=n+t_A.$$
--   The decoder budget is $T=\lfloor m/40\rfloor$ and the erasure cap is $\lfloor m/100\rfloor$. The thresholds (8) are
--   $$\eta_A=\min\{\eta_{\mathrm{MS}}/4,1/(40kN_0)\},\quad\kappa_{\mathrm{aud}}=\eta_A/2,\quad\kappa_{\mathrm{test}}=\eta_{\mathrm{MS}}/8,\quad\nu=\tfrac18\min\{\kappa_{\mathrm{aud}},\kappa_{\mathrm{test}}\}.$$
--   The complete-OT sizes (26) are $m_0$, $L_0$ (with $q=1$), $q_{\mathrm{bank}}=10L_0$, $m_{\mathrm{pre}}=\mathrm{Next}(100q_{\mathrm{bank}})$, $L_{\mathrm{pre}}$, and $L_{\mathrm{total}}=2L_{\mathrm{pre}}+L_0$. The constants (9), with $K=kN_0$, are
--   $$C_{\mathrm{size}}=1+18000(K+1),\quad c_{\mathrm{local}}=\frac1{100(K+1)},\quad c_{\mathrm{global}}=\frac{1}{100(K+1)C_{\mathrm{size}}},\quad\nu_{\mathrm{global}}=\frac{\nu}{C_{\mathrm{size}}}.$$
--   The module also defines the erasure tail (the probability, under honest uniform questions, that more than $\lfloor m/100\rfloor$ symbols are erased) and $\xi=6(0.047)-\log_2(64/63)$.
--
--   `AdmissibleConstants` holds when $\gamma,\eta_{\mathrm{MS}}>0$ satisfy the selector bound of Lemma 31 on $[0.047/56,1]$ with $\delta_*=1/2$, and $N_0\ge\max\{166,200/(k\gamma)\}$.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §3.2, p.27, (7)–(9); (26), p.56; Protocol 2 Step 6, p.30

import Mathlib
import Definitions.Def_DIObliviousTransfer_CodeFamily
import Definitions.Def_DIObliviousTransfer_SelectorBound

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §3.2, p.27: the
common schedule (7)–(9), and §7, p.56: the complete-OT sizes (26).

"Fix `a∗ = 0.047`, anchoring probability `δ∗ = 1/2`, and selector bounds `ρ_min = 1/8`,
`ρ_max = 1/2`. Apply Lemma 31 on the density interval `[a∗/[8(k + 1)], 1]`, and let
`γ, η_MS > 0` be its common guessing exponent and loss threshold. Choose the fixed integer
`N₀ ≥ max{166, ⌈200/(kγ)⌉}`. … put `s_λ = ⌈log₂²(λ + 2)⌉`, `m = Next(max{100q, 100ℓ, s_λ})`,
`n = kN₀m`, `t_A = ⌈m/200⌉`, `L = n + t_A`. (7) … decoder budget `T = ⌊m/40⌋`. Set
`η_A = min{η_MS/4, 1/(40kN₀)}`, `κ_aud = η_A/2`, `κ_test = η_MS/8`, `ν = (1/8) min{κ_aud, κ_test}`.
(8) … Write `K = kN₀` and set `C_size = 1 + 18000(K + 1)`, `c_local = 1/(100(K + 1))`,
`c_global = 1/(100(K + 1)C_size)`, `ν_global = ν/C_size`. (9)" (p.27)
"`m₀ = Next(max{100, 100ℓ, s_λ})`, `L₀ = kN₀m₀ + ⌈m₀/200⌉`, `q_bank = 10L₀`,
`m_pre = Next(100q_bank)`, `L_pre = kN₀m_pre + ⌈m_pre/200⌉`. (26)" (p.56)

**Formalization Note** (decision D16). The schedule is a function of the fixed integer `N₀` and
the loss threshold `η_MS`; the theorems quantify over every `γ, η_MS > 0` meeting the conclusion of
Lemma 31 on that interval and every integer `N₀ ≥ max{166, 200/(kγ)}` (for an integer `N₀` this is
the same as `N₀ ≥ ⌈200/(kγ)⌉`). Lengths are natural numbers; `⌈m/200⌉` is `(m + 199)/200`.
-/

/-- `k = 6` physical groups per code symbol. -/
def kk : ℕ := 6

/-- `a∗ = 0.047`. -/
noncomputable def aStar : ℝ := 0.047

/-- The anchoring probability `δ∗ = 1/2`. -/
noncomputable def deltaStar : ℝ := 1 / 2

/-- The code length of (7): `m = Next(max{100q, 100ℓ, s_λ})`. -/
noncomputable def mOf (lam ell q : ℕ) : ℕ := Next (max (max (100 * q) (100 * ell)) (sLam lam))

/-- `t_A = ⌈m/200⌉`. -/
def tAOf (m : ℕ) : ℕ := (m + 199) / 200

/-- `n = kN₀m`. -/
def nOf (N₀ m : ℕ) : ℕ := kk * N₀ * m

/-- `L = n + t_A`, the physical size of one invocation. -/
def LOf (N₀ m : ℕ) : ℕ := nOf N₀ m + tAOf m

/-- The decoder budget `T = ⌊m/40⌋`. -/
def TOf (m : ℕ) : ℕ := m / 40

/-- The erasure cap `⌊m/100⌋`. -/
def eraseCap (m : ℕ) : ℕ := m / 100

/-- `η_A = min{η_MS/4, 1/(40kN₀)}` of (8). -/
noncomputable def etaA (N₀ : ℕ) (ηMS : ℝ) : ℝ := min (ηMS / 4) (1 / (40 * kk * N₀))

/-- `κ_aud = η_A/2` of (8). -/
noncomputable def kappaAud (N₀ : ℕ) (ηMS : ℝ) : ℝ := etaA N₀ ηMS / 2

/-- `κ_test = η_MS/8` of (8). -/
noncomputable def kappaTest (ηMS : ℝ) : ℝ := ηMS / 8

/-- The local noise threshold `ν = (1/8) min{κ_aud, κ_test}` of (8). -/
noncomputable def nuOf (N₀ : ℕ) (ηMS : ℝ) : ℝ := (1 / 8) * min (kappaAud N₀ ηMS) (kappaTest ηMS)

/-- `m₀ = Next(max{100, 100ℓ, s_λ})` of (26). -/
noncomputable def m0Of (lam ell : ℕ) : ℕ := mOf lam ell 1

/-- `L₀ = kN₀m₀ + ⌈m₀/200⌉` of (26). -/
noncomputable def L0Of (N₀ lam ell : ℕ) : ℕ := LOf N₀ (m0Of lam ell)

/-- `q_bank = 10L₀` of (26). -/
noncomputable def qBank (N₀ lam ell : ℕ) : ℕ := 10 * L0Of N₀ lam ell

/-- `m_pre = Next(100q_bank)` of (26). -/
noncomputable def mPreOf (N₀ lam ell : ℕ) : ℕ := Next (100 * qBank N₀ lam ell)

/-- `L_pre = kN₀m_pre + ⌈m_pre/200⌉` of (26). -/
noncomputable def LPreOf (N₀ lam ell : ℕ) : ℕ := LOf N₀ (mPreOf N₀ lam ell)

/-- `L_total = 2L_pre + L₀`, the total number of device coordinates of one complete OT (27). -/
noncomputable def Ltotal (N₀ lam ell : ℕ) : ℕ := 2 * LPreOf N₀ lam ell + L0Of N₀ lam ell

/-- `C_size = 1 + 18000(K + 1)`, `K = kN₀`, of (9). -/
def Csize (N₀ : ℕ) : ℕ := 1 + 18000 * (kk * N₀ + 1)

/-- `c_local = 1/(100(K + 1))` of (9). -/
noncomputable def cLocal (N₀ : ℕ) : ℝ := 1 / (100 * ((kk * N₀ : ℕ) + 1 : ℝ))

/-- `c_global = 1/(100(K + 1)C_size)` of (9). -/
noncomputable def cGlobal (N₀ : ℕ) : ℝ := 1 / (100 * ((kk * N₀ : ℕ) + 1 : ℝ) * (Csize N₀ : ℝ))

/-- `ν_global = ν/C_size` of (9). -/
noncomputable def nuGlobal (N₀ : ℕ) (ηMS : ℝ) : ℝ := nuOf N₀ ηMS / (Csize N₀ : ℝ)

/-- One microblock fails the size rule of Protocol 2, Step 6 (p.30): among its `N₀ − 1`
non-audit positions with independent uniform trits `Y`, one of the two candidate sizes
`|{a : Y_a = b}|`, `b ∈ {0, 1}`, lies outside `[N₀/8, N₀/2]`. This is its probability. -/
noncomputable def pBlockFail (N₀ : ℕ) : ℝ := by
  classical
  exact (∑ y : Fin (N₀ - 1) → Fin 3,
    if ∃ b : Fin 3, b ≠ 2 ∧ ¬ ((N₀ : ℝ) / 8 ≤ ((Finset.univ.filter fun a => y a = b).card : ℝ) ∧
        ((Finset.univ.filter fun a => y a = b).card : ℝ) ≤ (N₀ : ℝ) / 2) then (1 : ℝ) else 0) /
    (3 : ℝ) ^ (N₀ - 1)

/-- The probability that a code symbol is erased (one of its `k` independent microblocks fails). -/
noncomputable def pSymbolErase (N₀ : ℕ) : ℝ := 1 - (1 - pBlockFail N₀) ^ kk

/-- The size error of Lemma 8: the probability, over honest uniform questions and audit coins,
that more than `⌊m/100⌋` of the `m` independent code symbols are erased. -/
noncomputable def erasureTail (N₀ m : ℕ) : ℝ :=
  ∑ s ∈ Finset.Ioc (eraseCap m) m,
    (m.choose s : ℝ) * pSymbolErase N₀ ^ s * (1 - pSymbolErase N₀) ^ (m - s)

/-- `ξ = 6(0.047) − log₂(64/63)` of Lemma 7 (p.26). -/
noncomputable def xi : ℝ := 6 * (0.047 : ℝ) - Real.logb 2 (64 / 63)

/-- The admissible constants of the schedule (decision D16): `γ, η_MS > 0` satisfy the
conclusion of Lemma 31 on the density interval `[a∗/[8(k+1)], 1] = [0.047/56, 1]` with
`δ∗ = 1/2` (`SelectorBound`), and the integer `N₀` satisfies `N₀ ≥ max{166, 200/(kγ)}`. -/
def AdmissibleConstants (γ ηMS : ℝ) (N₀ : ℕ) : Prop :=
  0 < γ ∧ 0 < ηMS ∧ SelectorBound deltaStar (aStar / (8 * (kk + 1))) 1 γ ηMS ∧
    (166 : ℝ) ≤ N₀ ∧ 200 / (kk * γ) ≤ (N₀ : ℝ)

end DIObliviousTransfer


