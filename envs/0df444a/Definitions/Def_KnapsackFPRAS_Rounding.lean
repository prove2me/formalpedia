-- Prove2me | Definitions.Def_KnapsackFPRAS_Rounding
-- name    : KnapsackFPRAS_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:48.331194+00:00
-- url     : https://prove2.me/theorems/8d1d2d3a-6cac-4cb7-8659-366ad8e235d6
-- title:
--   Weight classes $I_m$, spacings $s_m$, tiny items and the random rounding law
-- statement:
--   Fix a capacity $T$, weights $w_1,\dots,w_n$ and a power of two $B\ge2$. Put
--
--   $$
--   S:=T/B,\qquad \tau:=T/B^2 .
--   $$
--
--   For real $m>0$ the **weight class** is $I_m:=\{i\in[n]: T/m<w_i\le 2T/m\}$. The **ordinary classes** are $I_m$ for $m\in\{2,4,\dots,B^2\}$; the class $m=2^j$ has **rounding spacing**
--
--   $$
--   s_m := \frac{S}{2^{\lceil(\log_2 m)/2\rceil}} = \frac{S}{2^{\lceil j/2\rceil}} .
--   $$
--
--   The **tiny** items are $I_{\mathrm{tiny}}:=\{i: w_i\le\tau\}$. Under $1\le w_i\le T$ every item is tiny or in exactly one ordinary class.
--
--   Each weight is rounded independently to a random $a_i$:
--
--   1. for an ordinary item $i\in I_m$, write $w_i/s_m=\lfloor w_i/s_m\rfloor+\theta_i$ with $\theta_i\in[0,1)$; then $a_i=s_m\lfloor w_i/s_m\rfloor$ with probability $1-\theta_i$ and $a_i=s_m(\lfloor w_i/s_m\rfloor+1)$ with probability $\theta_i$;
--   2. for a tiny item, $a_i=\tau$ with probability $w_i/\tau$ and $a_i=0$ otherwise.
--
--   The law of the rounded vector $a=(a_1,\dots,a_n)$ is the product of these $n$ two-point laws.
--
--   **Formalization Note** The class $m=2^j$ is indexed by $j$, and $\lceil j/2\rceil$ is computed as $(j+1)/2$ in natural-number division. The class of an item is the least $j$ with $i\in I_{2^j}$ (classes are disjoint). An item that is neither tiny nor in a class keeps its weight; under the standing assumption (7) there is none. The rounding law is `Measure.pi` of the item laws, so independence across items is part of the definition, not an assumption.
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), §4.1 and §4.2, pp.14–15 (PDF pp.15–16), (14); Corollary 3.4, p.14 (PDF p.15) for $I_m$

import Mathlib

set_option autoImplicit false

namespace KnapsackFPRAS

open MeasureTheory

/-! # Weight classes and the random rounding

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), §4.1, p.14 (PDF p.15): "Set 𝑆 := 𝑇/𝐵, 𝜏 := 𝑇/𝐵²"; §4.2,
pp.14–15 (PDF pp.15–16): the ordinary classes `I_m := {i : T/m < wᵢ ≤ 2T/m}` with spacing
`s_m := S / 2^{⌈(log₂ m)/2⌉}` for `m ∈ {2, 4, …, B²}`, the tiny class `{i : wᵢ ≤ τ}`, and the
independent rounding of each weight. Corollary 3.4, p.14 (PDF p.15) uses the same `I_m` for real
`m ≥ 1`.

**Formalization Note.** `B` and `T` are natural numbers; the statements assume `B = 2^b` with
`b ≥ 1` and the standing assumption (7). The class `I_m` is defined for every real `m` with real
thresholds. An ordinary class `m = 2^j` is indexed by its exponent `j`, and
`⌈(log₂ 2^j)/2⌉ = ⌈j/2⌉ = (j + 1)/2` (natural-number division). `classExp T w i` is the least
`j` with `i ∈ I_{2^j}` (the classes are disjoint, so it is the class of `i`). Each item's rounded
weight has the two-point law of p.15: an ordinary item `i ∈ I_m` with `wᵢ/s_m = ⌊wᵢ/s_m⌋ + θᵢ`
goes to `s_m⌊wᵢ/s_m⌋` with probability `1 − θᵢ` and to `s_m(⌊wᵢ/s_m⌋ + 1)` with probability
`θᵢ`; a tiny item goes to `τ` with probability `wᵢ/τ` and to `0` otherwise. An item in no class
(impossible under (7)) keeps its weight. The law of the rounded vector `a` is the **product** of
these laws (`Measure.pi`): independence across items is part of the definition. -/

namespace Rounding

/-- The final rounding spacing `S := T/B`. -/
noncomputable def S (B T : ℕ) : ℝ := (T : ℝ) / B

/-- The finest rounding spacing `τ := T/B²`. -/
noncomputable def τ (B T : ℕ) : ℝ := (T : ℝ) / (B : ℝ) ^ 2

/-- The weight class `I_m := {i ∈ [n] : T/m < wᵢ ≤ 2T/m}` (real thresholds). -/
noncomputable def classIdx {n : ℕ} (T : ℕ) (w : Fin n → ℕ) (m : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (T : ℝ) / m < w i ∧ (w i : ℝ) ≤ 2 * T / m)

/-- The rounding spacing of the ordinary class `m = 2^j`:
`s_m := S / 2^{⌈(log₂ m)/2⌉} = S / 2^{⌈j/2⌉}`. -/
noncomputable def spacing (B T j : ℕ) : ℝ := S B T / (2 : ℝ) ^ ((j + 1) / 2)

/-- The tiny items `I_tiny := {i ∈ [n] : wᵢ ≤ τ}`. -/
noncomputable def tiny {n : ℕ} (B T : ℕ) (w : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (w i : ℝ) ≤ τ B T)

/-- The class exponent of item `i`: the least `j` with `i ∈ I_{2^j}` (`0` if there is none). -/
noncomputable def classExp {n : ℕ} (T : ℕ) (w : Fin n → ℕ) (i : Fin n) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, i ∈ classIdx T w ((2 : ℝ) ^ j) then Nat.find h else 0

/-- The two-point law taking the value `y` with probability `q` and `x` otherwise:
`Ber(y, x, q)`, with `q` projected onto `[0, 1]` (which changes nothing when `0 ≤ q ≤ 1`). -/
noncomputable def twoPoint (x y q : ℝ) : Measure ℝ :=
  ProbabilityTheory.bernoulliMeasure y x (Set.projIcc 0 1 zero_le_one q)

/-- The law of the rounded weight `aᵢ` of item `i` (p.15). -/
noncomputable def itemLaw {n : ℕ} (B T : ℕ) (w : Fin n → ℕ) (i : Fin n) : Measure ℝ := by
  classical
  exact
    if (w i : ℝ) ≤ τ B T then twoPoint 0 (τ B T) ((w i : ℝ) / τ B T)
    else if ∃ j : ℕ, i ∈ classIdx T w ((2 : ℝ) ^ j) then
      let s := spacing B T (classExp T w i)
      let f : ℝ := ⌊(w i : ℝ) / s⌋
      twoPoint (s * f) (s * (f + 1)) ((w i : ℝ) / s - f)
    else Measure.dirac (w i : ℝ)

instance itemLaw.isProbabilityMeasure {n : ℕ} (B T : ℕ) (w : Fin n → ℕ) (i : Fin n) :
    IsProbabilityMeasure (itemLaw B T w i) := by
  unfold itemLaw twoPoint
  split_ifs <;> infer_instance

/-- The law of the rounded weight vector `a = (a₁, …, aₙ)`: the product of the item laws, so the
items are rounded independently. -/
noncomputable def roundLaw {n : ℕ} (B T : ℕ) (w : Fin n → ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => itemLaw B T w i)

end Rounding

end KnapsackFPRAS


