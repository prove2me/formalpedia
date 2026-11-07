-- Prove2me | Definitions.Def_PolyEulerFlow_IsUniformClock
-- name    : PolyEulerFlow_IsUniformClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:21.697098+00:00
-- url     : https://prove2.me/theorems/702e2f94-3224-4231-badd-a2fc810ede57
-- title:
--   Scalar box (25), clock entry conditions (29), $\Delta_\varepsilon$, and the uniform-clock property of Lemma 31
-- statement:
--   The quantities of §§6.4–6.7 used by the clock and comparator milestones.
--
--   1. $\Delta_\varepsilon=(1+L)(\varepsilon^{1/4}+\nu)$ with $L=\log(1/\varepsilon)$ ((5), (33)).
--   2. The **scalar box** (25): $-\nu\le p_i\le1+\nu$, $\varepsilon/2\le\tau_i\le1+3\nu$, $|v_j|\le1+4\nu$.
--   3. The **entry conditions** (29) of phase $j$, with constants $A_0,B_0$ and $\mu_0=\varepsilon^{1/4}$: $p_j\ge9/10$, $|p_{j+1}|,|p_{j+2}|\le\mu_0$, $\varepsilon/2\le\tau_j\le A_0\varepsilon$, $\tau_{j+1}\le2\varepsilon$, $\tau_{j+2}\le B_0\varepsilon^{4/5}$.
--   4. The **uniform-clock property** for constants $A_0,B_0,C_{dur},C_{env},C_{next},D_{clk},\varepsilon_0$: all positive, and for $0<\varepsilon\le\varepsilon_0$, $0\le\nu\le\varepsilon^2$, every admissible mesh and every disturbance of level $\nu$, the initial clock satisfies (29) at phase $0$, and the clock orbit started in the clock box at the entry conditions of phase $j$ (at time $t_j=0$) has a next phase entry $t_{j+1}$ and a first time $t^b_j$ with $\tau_j\ge1/4$, such that (29) holds at $t_{j+1}$ for phase $j+1$; $L-C_{dur}\le t^b_j\le4L+C_{dur}$ and $0\le t_{j+1}-t^b_j\le D_{clk}$ (30); $p_j\ge9/10$ at every grid time up to $t_{j+1}-D_{clk}$; $\tau_{j+1}\le C_{next}\varepsilon$ on the phase; on the closed phase $|p_{j-1}(t)|\le C_{env}e^{-3t/8}+C_{env}\varepsilon^{37/20}+C_{env}\nu$ and $|p_{j+2}(t)|\le C_{env}\mu_0$ (31); before $t^b_j$, $|p_{j+1}(t)|\le C_{env}(\mu_0+\tau_j(t)^4+\nu)$ and $\tau_j(t)\le C_{env}\varepsilon e^{(1+4\nu)t}$ (32).
--   5. A **comparator orbit** (Lemma 34): $v_{k+1}=v_k+\eta_k\big((1-p_k)\tfrac{v_k-v_k^3}2+p_k(u_k-v_k)\big)+\eta_k\xi_k$ along an admissible mesh, with $-\nu\le p_k\le1+\nu$, $|v_k|\le1+4\nu$, $|u_k|\le1$, $|\xi_k|\le\nu$, where the gate $p$ and the test value $u$ are given sequences.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), (25), Lemma 28, p.28 (PDF 30); §6.5 and Lemma 31, pp.29–30 (PDF 31–32); (33), p.30 (PDF 32); Lemma 34, p.31 (PDF 33)

import Definitions.Def_PolyEulerFlow_compiledField
import Definitions.Def_PolyEulerFlow_eulerOrbit

namespace PolyEulerFlow

/-- `∆ε = (1 + L)(ε^{1/4} + ν)`, `L = log(1/ε)`: (5), p.10, and (33), p.30. -/
noncomputable def deltaEps (ε ν : ℝ) : ℝ :=
  (1 + Real.log (1 / ε)) * (ε ^ ((1 : ℝ) / 4) + ν)

/-- The clock part of the scalar box (25), p.28: `-ν ≤ p_i ≤ 1 + ν`, `ε/2 ≤ τ_i ≤ 1 + 3ν`. -/
def clockBox (ε ν : ℝ) (X : ClockState) : Prop :=
  ∀ i, -ν ≤ X (.inl i) ∧ X (.inl i) ≤ 1 + ν ∧ ε / 2 ≤ X (.inr i) ∧ X (.inr i) ≤ 1 + 3 * ν

/-- The scalar box (25), p.28, of a state of the compiled system: also `|v_j| ≤ 1 + 4ν`. -/
def scalarBox {m g : ℕ} (ε ν : ℝ) (Z : CompiledState m g) : Prop :=
  clockBox ε ν (clockPart Z) ∧ ∀ j, |compV Z j| ≤ 1 + 4 * ν

/-- The entry conditions (29) of phase `j`, p.30, with `µ₀ = ε^{1/4}`. -/
def clockEntry (A0 B0 ε : ℝ) (j : Fin 4) (X : ClockState) : Prop :=
  9 / 10 ≤ X (.inl j) ∧ |X (.inl (j + 1))| ≤ ε ^ ((1 : ℝ) / 4) ∧ |X (.inl (j + 2))| ≤ ε ^ ((1 : ℝ) / 4) ∧
    ε / 2 ≤ X (.inr j) ∧ X (.inr j) ≤ A0 * ε ∧ X (.inr (j + 1)) ≤ 2 * ε ∧
    X (.inr (j + 2)) ≤ B0 * ε ^ ((4 : ℝ) / 5)

/-- The clock bit `p_i` as a function of a clock state. -/
def clockBit (i : Fin 4) (X : ClockState) : ℝ :=
  X (.inl i)

/-- The body of Lemma 31 (Uniform clock), p.30, for given constants. Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…), Lemma 31, p.30.
For `0 < ε ≤ ε₀`, `0 ≤ ν ≤ ε²`, every admissible mesh and permitted disturbance: from a state in the clock box satisfying (29) at phase `j`, the orbit
has a next phase entry `k1` and a first index `kb > 0` with `τ_j ≥ 1/4`; the conditions (29) hold at `k1` with `j + 1`; (30) holds; `p_j ≥ 9/10` outside a terminal
interval of length at most `Dclk`; the next timer is at most `Cnext ε` on the phase; (31) holds on the closed phase; (32) holds before `kb`. The initial clock satisfies (29) at `j = 0`.
**Formalization Note.** Phase `j` starts at index `0`: a later phase is the orbit of the shifted mesh and disturbance. "O(ε)" in the lemma is `Cnext ε`. The mesh is variable (Corollary 39, p.34). -/
def IsUniformClock (A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ) : Prop :=
  0 < A0 ∧ 0 < B0 ∧ 0 < Cdur ∧ 0 < Cenv ∧ 0 < Cnext ∧ 0 < Dclk ∧ 0 < ε0 ∧
  ∀ ε ν : ℝ, 0 < ε → ε ≤ ε0 → 0 ≤ ν → ν ≤ ε ^ 2 →
    clockEntry A0 B0 ε 0 (initialClock ε) ∧
    ∀ (η : ℕ → ℝ) (ξ : ℕ → ClockState) (X0 : ClockState) (j : Fin 4),
      IsAdmissibleMesh η → IsPermittedDisturbance ν ξ → clockBox ε ν X0 → clockEntry A0 B0 ε j X0 →
      let z := eulerOrbit (clockField ε) X0 η ξ
      let t := physTime η
      let L := Real.log (1 / ε)
      ∃ k1 kb : ℕ,
        IsFirstAfter (AboveThreshold clockBit (j + 1)) z 0 k1 ∧
        IsFirstAfter (fun X => (1 : ℝ) / 4 ≤ X (.inr j)) z 0 kb ∧
        clockEntry A0 B0 ε (j + 1) (z k1) ∧
        L - Cdur ≤ t kb ∧ t kb ≤ 4 * L + Cdur ∧
        0 ≤ t k1 - t kb ∧ t k1 - t kb ≤ Dclk ∧
        (∀ k ≤ k1, t k ≤ t k1 - Dclk → 9 / 10 ≤ z k (.inl j)) ∧
        (∀ k ≤ k1, z k (.inr (j + 1)) ≤ Cnext * ε) ∧
        (∀ k ≤ k1,
          |z k (.inl (j - 1))| ≤ Cenv * Real.exp (-(3 / 8) * t k) + Cenv * ε ^ ((37 : ℝ) / 20) + Cenv * ν ∧
          |z k (.inl (j + 2))| ≤ Cenv * ε ^ ((1 : ℝ) / 4)) ∧
        (∀ k < kb,
          |z k (.inl (j + 1))| ≤ Cenv * (ε ^ ((1 : ℝ) / 4) + z k (.inr j) ^ 4 + ν) ∧
          z k (.inr j) ≤ Cenv * ε * Real.exp ((1 + 4 * ν) * t k))

/-- A comparator orbit of Lemma 34, p.31: `v⁺ = v + η((1 - p)(v - v³)/2 + p(u - v)) + ηξ_v`, `|ξ_v| ≤ ν`, on the scalar box
(`-ν ≤ p ≤ 1 + ν`, `|v| ≤ 1 + 4ν`), with `|u| ≤ 1`, along an admissible mesh. The gate `p` and the test value `u` are given sequences,
not state variables ("The symbol u denotes the value of its test, which depends on time", p.31). -/
def IsComparatorOrbit (ν : ℝ) (η p u ξv v : ℕ → ℝ) : Prop :=
  IsAdmissibleMesh η ∧
  ∀ k, v (k + 1) = v k + η k * ((1 - p k) * (v k - v k ^ 3) / 2 + p k * (u k - v k)) + η k * ξv k ∧
    -ν ≤ p k ∧ p k ≤ 1 + ν ∧ |v k| ≤ 1 + 4 * ν ∧ |u k| ≤ 1 ∧ |ξv k| ≤ ν

end PolyEulerFlow


