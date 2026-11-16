-- Prove2me | Definitions.Def_RelatedSchedFPTAS796_Main_Supplement_Objectives
-- name    : RelatedSchedFPTAS796_Main_Supplement_Objectives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:45.270632+00:00
-- url     : https://prove2.me/theorems/43f72b85-f432-4f01-8cc5-69ff85d12cf4
-- title:
--   Well-behaved load objectives and both objective FPTAS predicates
-- statement:
--   For a fixed dimension $m$, a load objective $F$ is defined on the entire nonnegative real orthant and is nonnegative there. It is coordinatewise nondecreasing when $x\le y$ implies $F(x)\le F(y)$ on that orthant. Relative stability means that there is a fixed $K\ge0$ such that, for every real $0<\eta<1$ and nonnegative real vectors $x,y$,
--   $$
--   (1-\eta)x\le y\le(1+\eta)x\ \Longrightarrow\ (1-K\eta)F(x)\le F(y)\le(1+K\eta)F(x).
--   $$
--   Well-behavedness also requires one deterministic finite program $E$ of the published word RAM and fixed natural constants $b_e,C_e,c_e$. On every nonnegative rational vector $x$, rational $\eta\in(0,1)$, and width $w\ge b_e(\lfloor\log_2(m+M+2)\rfloor+1)$, it returns a nonnegative rational estimate $v$ with $(1-\eta)F(x)\le v\le(1+\eta)F(x)$ in at most $C_e\log_2(2/\eta)^{c_e}$ steps. Here $M$ is the largest absolute input word. Input is the coordinates' numerator/denominator pairs followed by those of $\eta$; output cells 0,1 contain a numerator and a positive denominator. Evaluation and output are charged in the existing machine.
--
--   The scheduling value is $F$ at the real vector of the published rational loads. For either optimization direction, the FPTAS predicate requires one program and constants $b,C,c$ before all instances, positive rational job sizes and speeds, and rational $\varepsilon,q\in(0,1)$. Every run halts within $C(n+(1/\varepsilon)^{m-1})H_c$, at every published admissible width. With probability at least $1-q$ it outputs an original schedule $\sigma$ such that
--   $$
--   F(L(\sigma))\le(1+\varepsilon)F(L(\tau))\quad\hbox{for all schedules }\tau
--   $$
--   in minimization, or $F(L(\sigma))\ge(1-\varepsilon)F(L(\tau))$ for all $\tau$ in maximization. Here $H_c=(\log_2(n+2)\log_2(2/\varepsilon)\log_2(2/q))^c$. These interfaces retain empty jobs, zero objective values, and different programs for the two directions; they support Appendix D without imposing continuity, convexity, homogeneity or exact evaluation.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.30, §1.1 lines 88–93, Appendix D lines 930–939, Theorem 1.2

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main.Supplement

open MatroidSensOracle

/-- Input to a fixed objective evaluator: the rational vector, followed by accuracy. Dimension
is fixed with the program. Source: pp.3,30, lines 88–93,936–939. -/
def evalInput {m : ℕ} (x : Fin m → ℚ) (η : ℚ) : List ℤ :=
  ratVecWords x ++ ratWords η

/-- A nonnegative rational estimate in output cells 0,1. The denominator must be positive. -/
def OutputsEstimate {w : ℕ} (mem : ℤ → BitVec w) (v : ℝ) : Prop :=
  0 < (mem 1).toNat ∧ v = ((mem 0).toNat : ℝ) / ((mem 1).toNat : ℝ)

/-- Relative stability is on the entire real orthant, including its boundary. The evaluator is
one deterministic finite program of the published RAM; its execution and output are charged.
All constants are fixed before the rational input, tolerance and word width. -/
def WellBehaved {m : ℕ} (F : (Fin m → ℝ) → ℝ) : Prop :=
  (∀ x ∈ nonneg m, 0 ≤ F x) ∧
  (∃ K : ℝ, 0 ≤ K ∧ ∀ (η : ℝ) (x y : Fin m → ℝ),
    0 < η → η < 1 → x ∈ nonneg m → y ∈ nonneg m →
    (∀ i, (1 - η) * x i ≤ y i ∧ y i ≤ (1 + η) * x i) →
      (1 - K * η) * F x ≤ F y ∧ F y ≤ (1 + K * η) * F x) ∧
  ∃ (E : List Instr) (b C c : ℕ), CoinFree E ∧
    ∀ (x : Fin m → ℚ) (η : ℚ), (∀ i, 0 ≤ x i) → 0 < η → η < 1 →
      ∀ w : ℕ, widthMin b m (maxWord (evalInput x η)) ≤ w →
        ∀ ω : Coins, ∃ (mem : ℤ → BitVec w) (v : ℝ),
          runFor E w (evalInput x η) (C * Real.logb 2 (2 / (η : ℝ)) ^ c) ω = some mem ∧
          OutputsEstimate mem v ∧
          (1 - (η : ℝ)) * F (ratToReal x) ≤ v ∧
          v ≤ (1 + (η : ℝ)) * F (ratToReal x)

/-- Coordinatewise nondecreasing on the nonnegative orthant, without strictness. -/
def NondecreasingObjective {m : ℕ} (F : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ x ∈ nonneg m, ∀ y ∈ nonneg m, x ≤ y → F x ≤ F y

/-- The objective at the real vector of the published rational machine loads. -/
noncomputable def scheduleValue {n m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (p : Fin n → ℚ) (s : Fin m → ℚ) (σ : Fin n → Fin m) : ℝ :=
  F (fun i => (load p s σ i : ℝ))

/-- `maximize = false`: value at most `(1+ε)` times every feasible value.
`maximize = true`: value at least `(1−ε)` times every feasible value (p.32 line 1036).
This includes zero optima and empty job sets without dividing by an optimum. -/
def ObjectiveApprox {n m : ℕ} (maximize : Bool) (F : (Fin m → ℝ) → ℝ)
    (p : Fin n → ℚ) (s : Fin m → ℚ) (ε : ℚ) (σ : Fin n → Fin m) : Prop :=
  ∀ τ : Fin n → Fin m,
    if maximize then (1 - (ε : ℝ)) * scheduleValue F p s τ ≤ scheduleValue F p s σ
    else scheduleValue F p s σ ≤ (1 + (ε : ℝ)) * scheduleValue F p s τ

/-- One fixed program and fixed constants, before every instance and every rational ε,q.
Both directions use the same published inputs, time, width and true schedule outputs. -/
def ObjectiveFPTAS (m : ℕ) (F : (Fin m → ℝ) → ℝ) (maximize : Bool) : Prop :=
  ∃ (P : List Instr) (b C c : ℕ), ∀ (n : ℕ) (p : Fin n → ℚ) (s : Fin m → ℚ) (ε q : ℚ),
    (∀ j, 0 < p j) → (∀ i, 0 < s i) → 0 < ε → ε < 1 → 0 < q → q < 1 →
    ∀ w : ℕ, widthMin b n (maxWord (fptasInput p s ε q)) ≤ w →
      HaltsWithin P w (fptasInput p s ε q) (fptasTime C c n m ε q) ∧
      FailsAtMost P w (fptasInput p s ε q) (fptasTime C c n m ε q)
        (fun mem => ∃ σ : Fin n → Fin m,
          OutputsSchedule mem σ ∧ ObjectiveApprox maximize F p s ε σ) q

end RelatedSchedFPTAS796.Main.Supplement


