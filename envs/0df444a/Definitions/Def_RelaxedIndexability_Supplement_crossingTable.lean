-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_crossingTable
-- name    : RelaxedIndexability_Supplement_crossingTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:02:56.594398+00:00
-- url     : https://prove2.me/theorems/4f4351af-8ace-5138-b511-ee1b6c065a28
-- title:
--   The case table of Theorem EC.1 for the first crossing time (corrected)
-- statement:
--   The cases of Theorem EC.1 as propositions about a sequence $h$ (the $k$-step reward function of a belief $\omega$), a threshold value $r=r^*=\omega^*B'$ and a value $L\in\mathbb N\cup\{+\infty\}$ (the first crossing time $L(\omega,\omega^*)$):
--
--   1. `InitialCases`: (EC.46), $L=0$ if $h(0)>r^*$, $L=1$ if $h(1)>r^*\ge h(0)$, $L=2$ if $h(2)>r^*\ge\max\{h(0),h(1)\}$;
--   2. `DiagonalizableCases`: the cases 1.1–1.22 for $h(k)=a_1b_1^k+a_2b_2^k+c$, and `IsListed`, the disjunction of their hypotheses used for case 1.23;
--   3. `JordanCases`: the cases 2.1–2.5 for $h(k)=ab^k+ckb^{k-1}+d$;
--   4. `ComplexCases`: the cases 3.1–3.8 for $h(k)=a'A^k\sin(k\theta+b')+c'$, with $d'=(r^*-c')/a'$.
--
--   Each case states the printed hypothesis and the printed value of $L$ in each printed branch, with the auxiliary quantities $z_0=-\frac{a_2(1-b_2)}{a_1(1-b_1)}$, $z_1=-\frac{a_2(1-b_2^2)}{a_1(1-b_1^2)}$, $z_2=\frac{a_2(b_2^2-1)}{a_1(b_1^2-1)}$, $z_3=\frac{ab-ab^2-cb}{c(b-1)}$, $z_4=\frac{ab-ab^3-2cb^2}{c(b^2-1)}$, the even floor $\lfloor x\rfloor_e$ (the largest even integer $\le x$) and the odd floor $\lfloor x\rfloor_o$ (the largest odd integer $\le x$). "$L=\min S$" means that $S$ has a least element and $L$ equals it, and "$L=$ an integer formula" means that $L$ is finite and equal to it.
--
--   Five printed entries are false and are replaced by the values that the paper's proof gives: in 1.3 and 1.5 the finite value is $\lfloor\log_{b}\frac{c-r^*}{-a}\rfloor+1$, not $+2$; in 1.12 the logarithm base is $|b_1|/b_2$ and the floor is the even floor $\lfloor\cdot\rfloor_e$; in 1.17 the floor is the odd floor $\lfloor\cdot\rfloor_o$; in 2.1, $h(\lceil z_3\rceil)$ replaces $h(z_3+1)$. Misprints read as intended: base $|b_1|/b_2$ in 1.13; both inequalities in 1.7; $r^*$ for $\omega^*$ in 1.19 and 1.22; the missing $\max$ in 1.21 and 2.4; $b'$ for $b$ in 3.7 and 3.8. Case 2.5 ("forms similar to those in (1.1)–(1.6)") is written out: for $c=0$ the forms of 1.5–1.6 with $(a_1,b_1,c):=(a,b,d)$, and for $b=0$ the form of 1.4.
--
--   **Formalization Note** `Real.logb b x` is $\log_bx$. In every case each logarithm has a positive argument and a positive base different from $1$. An integer index of $h$ inside a condition is converted with `Int.toNat`; under the condition beside it the integer is nonnegative. In 3.1 "$\max\{h(k):0\le k<\lceil\log_Ad'\rceil\}>r^*$" is an existential and "$\le r^*$" a universal statement.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Theorem EC.1, (EC.46)–(EC.65), pp.ec13–ec17; proofs of 1.3, 1.12, 1.17, 2.1, pp.ec18, ec20, ec21, ec23

import Mathlib

open Real

namespace RelaxedIndexability.Supplement

/-- `L = z` for an integer formula `z`: `L` is finite and equals `z` (so `z ≥ 0`). -/
def EqInt (L : ℕ∞) (z : ℤ) : Prop :=
  ∃ n : ℕ, L = n ∧ (n : ℤ) = z

/-- `L = min S`: `S` has a least element and `L` is that element (so `S` is nonempty). -/
def EqMin (L : ℕ∞) (S : Set ℕ) : Prop :=
  ∃ n : ℕ, L = n ∧ IsLeast S n

/-- `⌊x⌋_e`, the maximum even integer not exceeding `x` (p.ec16). -/
noncomputable def evenFloor (x : ℝ) : ℤ := 2 * ⌊x / 2⌋

/-- `⌊x⌋_o`, the maximum odd integer not exceeding `x` (p.ec16). -/
noncomputable def oddFloor (x : ℝ) : ℤ := 2 * ⌊(x - 1) / 2⌋ + 1

/-- `z₀ = −a₂(1 − b₂)/(a₁(1 − b₁))`, cases 1.8 and 1.9 (p.ec14). -/
noncomputable def zZero (a₁ b₁ a₂ b₂ : ℝ) : ℝ := -(a₂ * (1 - b₂) / (a₁ * (1 - b₁)))

/-- `z₁ = −a₂(1 − b₂²)/(a₁(1 − b₁²))`, cases 1.12, 1.13, 1.20 and 1.21 (pp.ec15–ec16). -/
noncomputable def zOne (a₁ b₁ a₂ b₂ : ℝ) : ℝ := -(a₂ * (1 - b₂ ^ 2) / (a₁ * (1 - b₁ ^ 2)))

/-- `z₂ = a₂(b₂² − 1)/(a₁(b₁² − 1))`, cases 1.17 and 1.18 (p.ec15). -/
noncomputable def zTwo (a₁ b₁ a₂ b₂ : ℝ) : ℝ := a₂ * (b₂ ^ 2 - 1) / (a₁ * (b₁ ^ 2 - 1))

/-- `z₃ = (ab − ab² − cb)/(c(b − 1))`, cases 2.1 and 2.2 (p.ec16). -/
noncomputable def zThree (a b c : ℝ) : ℝ := (a * b - a * b ^ 2 - c * b) / (c * (b - 1))

/-- `z₄ = (ab − ab³ − 2cb²)/(c(b² − 1))`, cases 2.3 and 2.4 (p.ec17). -/
noncomputable def zFour (a b c : ℝ) : ℝ :=
  (a * b - a * b ^ 3 - 2 * c * b ^ 2) / (c * (b ^ 2 - 1))

/-- **(EC.46)** (Liu, arXiv:2107.11939v4, Theorem EC.1, p.ec13): the first three values of
`L = L(ω, ω*)`, with `h` the `k`-step reward function of `ω` and `r = r* = ω* B′`. -/
structure InitialCases (h : ℕ → ℝ) (r : ℝ) (L : ℕ∞) : Prop where
  /-- `L = 0` if `h(0) > r*`. -/
  zero : r < h 0 → L = 0
  /-- `L = 1` if `h(1) > r* ≥ h(0)`. -/
  one : r < h 1 → h 0 ≤ r → L = 1
  /-- `L = 2` if `h(2) > r* ≥ max{h(0), h(1)}`. -/
  two : r < h 2 → max (h 0) (h 1) ≤ r → L = 2

/-- **Cases 1.1–1.22 of Theorem EC.1, corrected** (Liu, arXiv:2107.11939v4, pp.ec14–ec16), for
`h(k) = a₁ b₁^k + a₂ b₂^k + c`.

**Formalization Note.** `Real.logb b x` is `log_b x`, and every logarithm below has a positive
argument and a positive base different from `1` in its case. In the conditions, an integer index
of `h` is passed through `Int.toNat`; under the condition beside it that integer is nonnegative.
Corrections: `+ 1` for the printed `+ 2` in 1.3 and 1.5; base `|b₁|/b₂` and the even floor in 1.12;
base `|b₁|/b₂` in 1.13; the odd floor in 1.17. Misprints read as intended: both inequalities in
1.7, `r*` for `ω*` in 1.19 and 1.22, the missing `max` in 1.21. -/
structure DiagonalizableCases (h : ℕ → ℝ) (r : ℝ) (L : ℕ∞) (a₁ b₁ a₂ b₂ c : ℝ) : Prop where
  /-- Case 1.1, (EC.47). -/
  case_1_1 : b₁ = b₂ → b₁ ≠ 0 → 0 < b₁ → a₁ + a₂ < 0 →
    (h 0 ≤ r ∧ r < c → EqInt L (⌊logb b₁ ((c - r) / -(a₁ + a₂))⌋ + 1)) ∧
    (c ≤ r → L = ⊤)
  /-- Case 1.2. -/
  case_1_2 : b₁ = b₂ → b₁ ≠ 0 → (b₁ < 0 ∨ 0 ≤ a₁ + a₂) →
    max (h 0) (h 1) ≤ r → L = ⊤
  /-- Case 1.3, (EC.48), corrected: `+ 1` for the printed `+ 2`. -/
  case_1_3 : a₁ * b₁ = 0 → 0 < b₂ → a₂ < 0 →
    (max (h 0) (h 1) ≤ r ∧ r < c → EqInt L (⌊logb b₂ ((c - r) / -a₂)⌋ + 1)) ∧
    (max (h 0) c ≤ r → L = ⊤)
  /-- Case 1.4. -/
  case_1_4 : a₁ * b₁ = 0 → (b₂ ≤ 0 ∨ 0 ≤ a₂) →
    max (max (h 0) (h 1)) (h 2) ≤ r → L = ⊤
  /-- Case 1.5, (EC.49), corrected: `+ 1` for the printed `+ 2`. -/
  case_1_5 : a₂ * b₂ = 0 → 0 < b₁ → a₁ < 0 →
    (max (h 0) (h 1) ≤ r ∧ r < c → EqInt L (⌊logb b₁ ((c - r) / -a₁)⌋ + 1)) ∧
    (max (h 0) c ≤ r → L = ⊤)
  /-- Case 1.6. -/
  case_1_6 : a₂ * b₂ = 0 → (b₁ ≤ 0 ∨ 0 ≤ a₁) →
    max (max (h 0) (h 1)) (h 2) ≤ r → L = ⊤
  /-- Case 1.7. -/
  case_1_7 : 0 < a₁ → 0 < a₂ → 0 < b₁ → 0 < b₂ →
    h 0 ≤ r → h 1 ≤ r → L = ⊤
  /-- Case 1.8, (EC.50). -/
  case_1_8 : a₁ < 0 → 0 < a₂ → b₂ < b₁ → 0 < b₂ →
    (h 0 ≤ r ∧ r < c →
      EqMin L {k : ℕ | max ⌈logb (b₁ / b₂) (zZero a₁ b₁ a₂ b₂)⌉ 0 < (k : ℤ) ∧ r < h k}) ∧
    (max (h 0) c ≤ r → L = ⊤)
  /-- Case 1.9, (EC.51). -/
  case_1_9 : a₁ < 0 → 0 < a₂ → b₁ < b₂ → 0 < b₁ →
    (zZero a₁ b₁ a₂ b₂ < 1 ∧
        r < h (⌊logb (b₁ / b₂) (zZero a₁ b₁ a₂ b₂)⌋ + 1).toNat ∧ h 0 ≤ r →
      EqMin L {k : ℕ | 0 < k ∧ (k : ℤ) ≤ ⌊logb (b₁ / b₂) (zZero a₁ b₁ a₂ b₂)⌋ + 1 ∧ r < h k}) ∧
    ((1 ≤ zZero a₁ b₁ a₂ b₂ ∧ h 0 ≤ r) ∨
        (zZero a₁ b₁ a₂ b₂ < 1 ∧ h (⌊logb (b₁ / b₂) (zZero a₁ b₁ a₂ b₂)⌋ + 1).toNat ≤ r) →
      L = ⊤)
  /-- Case 1.10. -/
  case_1_10 : b₁ < 0 → 0 < a₁ → 0 < a₂ → 0 < b₂ →
    h 0 ≤ r → L = ⊤
  /-- Case 1.11. -/
  case_1_11 : a₁ < 0 → b₁ < 0 → 0 < a₂ → 0 < b₂ →
    max (h 0) (h 1) ≤ r → L = ⊤
  /-- Case 1.12, (EC.52), corrected: base `|b₁|/b₂` and the even floor. -/
  case_1_12 : a₂ < 0 → b₁ < 0 → 0 < a₁ → 0 < b₂ → b₂ < |b₁| →
    (1 ≤ zOne a₁ b₁ a₂ b₂ ∧
        r < h (evenFloor (logb (|b₁| / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat ∧ h 0 ≤ r →
      EqMin L {k : ℕ | 0 < k ∧
        (k : ℤ) ≤ evenFloor (logb (|b₁| / b₂) (zOne a₁ b₁ a₂ b₂)) + 2 ∧ r < h k}) ∧
    ((zOne a₁ b₁ a₂ b₂ < 1 ∧ h 0 ≤ r) ∨
        (1 ≤ zOne a₁ b₁ a₂ b₂ ∧
          h (evenFloor (logb (|b₁| / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat ≤ r) →
      L = ⊤)
  /-- Case 1.13, (EC.53), with base `|b₁|/b₂`. -/
  case_1_13 : a₂ < 0 → b₁ < 0 → 0 < a₁ → 0 < b₂ → |b₁| < b₂ →
    (h 0 ≤ r ∧ r < c →
      EqMin L {k : ℕ | max ⌈logb (|b₁| / b₂) (zOne a₁ b₁ a₂ b₂)⌉ 1 ≤ (k : ℤ) ∧ r < h k}) ∧
    (max (h 0) c ≤ r → L = ⊤)
  /-- Case 1.14, (EC.54). -/
  case_1_14 : a₂ < 0 → b₁ < 0 → 0 < a₁ → 0 < b₂ → |b₁| = b₂ →
    (h 0 ≤ r ∧ r < c → EqMin L {k : ℕ | 1 ≤ k ∧ r < h k}) ∧
    (max (h 0) c ≤ r → L = ⊤)
  /-- Case 1.15. -/
  case_1_15 : b₁ < 0 → b₂ < 0 → 0 < a₁ → 0 < a₂ →
    h 0 ≤ r → L = ⊤
  /-- Case 1.16, (EC.55). -/
  case_1_16 : 0 < b₁ → 0 < b₂ → a₁ < 0 → a₂ < 0 →
    (r < c → EqMin L {k : ℕ | 0 ≤ k ∧ r < h k}) ∧
    (c ≤ r → L = ⊤)
  /-- Case 1.17, (EC.56), corrected: the odd floor. -/
  case_1_17 : a₁ < 0 → a₂ < 0 → b₁ < 0 → 0 < b₂ → b₂ < |b₁| →
    (-b₁ / b₂ < zTwo a₁ b₁ a₂ b₂ ∧
        r < h (oddFloor (logb (-b₁ / b₂) (zTwo a₁ b₁ a₂ b₂)) + 2).toNat ∧ h 0 ≤ r →
      EqMin L {k : ℕ | 0 < k ∧
        (k : ℤ) ≤ oddFloor (logb (-b₁ / b₂) (zTwo a₁ b₁ a₂ b₂)) + 2 ∧ r < h k}) ∧
    ((zTwo a₁ b₁ a₂ b₂ ≤ -b₁ / b₂ ∧ h 1 ≤ r) ∨
        (-b₁ / b₂ < zTwo a₁ b₁ a₂ b₂ ∧
          h (oddFloor (logb (-b₁ / b₂) (zTwo a₁ b₁ a₂ b₂)) + 2).toNat ≤ r) →
      L = ⊤)
  /-- Case 1.18, (EC.57). -/
  case_1_18 : a₁ < 0 → a₂ < 0 → b₁ < 0 → 0 < b₂ → |b₁| < b₂ →
    (h 1 ≤ r ∧ r < c →
      EqMin L {k : ℕ | max ⌈logb (-b₁ / b₂) (zTwo a₁ b₁ a₂ b₂)⌉ 1 ≤ (k : ℤ) ∧ r < h k}) ∧
    (max (h 1) c ≤ r → L = ⊤)
  /-- Case 1.19, (EC.58), with `h(k) > r*` for the misprinted `h(k) > ω*`. -/
  case_1_19 : a₁ < 0 → a₂ < 0 → b₁ < 0 → 0 < b₂ → |b₁| = b₂ →
    (h 1 ≤ r ∧ r < c → EqMin L {k : ℕ | 1 < k ∧ r < h k}) ∧
    (max (h 1) c ≤ r → L = ⊤)
  /-- Case 1.20, (EC.59). -/
  case_1_20 : a₂ < 0 → b₁ < 0 → b₂ < 0 → 0 < a₁ → |b₂| < |b₁| →
    (1 < zOne a₁ b₁ a₂ b₂ ∧ h 0 ≤ r ∧
        r < h (evenFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat →
      EqMin L {k : ℕ | 1 ≤ k ∧
        (k : ℤ) ≤ evenFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2 ∧ r < h k}) ∧
    ((1 < zOne a₁ b₁ a₂ b₂ ∧
          max (max (h 0) (h 1))
            (h (evenFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat) ≤ r) ∨
        (zOne a₁ b₁ a₂ b₂ ≤ 1 ∧ h 0 ≤ r) →
      L = ⊤)
  /-- Case 1.21, (EC.60), with the missing `max` restored. -/
  case_1_21 : a₂ < 0 → b₁ < 0 → b₂ < 0 → 0 < a₁ → |b₁| < |b₂| →
    (zOne a₁ b₁ a₂ b₂ < b₁ / b₂ ∧ h 0 ≤ r ∧
        r < h (oddFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat →
      EqMin L {k : ℕ | 1 ≤ k ∧
        (k : ℤ) ≤ oddFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2 ∧ r < h k}) ∧
    ((b₁ / b₂ ≤ zOne a₁ b₁ a₂ b₂ ∧ max (h 0) (h 1) ≤ r) ∨
        (zOne a₁ b₁ a₂ b₂ < b₁ / b₂ ∧
          max (max (h 0) (h 1))
            (h (oddFloor (logb (b₁ / b₂) (zOne a₁ b₁ a₂ b₂)) + 2).toNat) ≤ r) →
      L = ⊤)
  /-- Case 1.22, with `r* ≥ h(1)` for the misprinted `ω* ≥ h(1)`. -/
  case_1_22 : a₂ < 0 → b₁ < 0 → b₂ < 0 → a₁ < 0 →
    h 1 ≤ r → L = ⊤

/-- **Case 1.23** (p.ec16, "any other case, which is symmetric to one of the above"): the
parameters `(a₁, b₁, a₂, b₂)` satisfy the hypothesis of one of the cases 1.1–1.22. A tuple that does
not is one whose exchange `(a₂, b₂, a₁, b₁)` does. -/
def IsListed (a₁ b₁ a₂ b₂ : ℝ) : Prop :=
  (b₁ = b₂ ∧ b₁ ≠ 0 ∧ 0 < b₁ ∧ a₁ + a₂ < 0) ∨            -- 1.1
  (b₁ = b₂ ∧ b₁ ≠ 0 ∧ (b₁ < 0 ∨ 0 ≤ a₁ + a₂)) ∨           -- 1.2
  (a₁ * b₁ = 0 ∧ 0 < b₂ ∧ a₂ < 0) ∨                       -- 1.3
  (a₁ * b₁ = 0 ∧ (b₂ ≤ 0 ∨ 0 ≤ a₂)) ∨                     -- 1.4
  (a₂ * b₂ = 0 ∧ 0 < b₁ ∧ a₁ < 0) ∨                       -- 1.5
  (a₂ * b₂ = 0 ∧ (b₁ ≤ 0 ∨ 0 ≤ a₁)) ∨                     -- 1.6
  (0 < a₁ ∧ 0 < a₂ ∧ 0 < b₁ ∧ 0 < b₂) ∨                   -- 1.7
  (a₁ < 0 ∧ 0 < a₂ ∧ b₂ < b₁ ∧ 0 < b₂) ∨                  -- 1.8
  (a₁ < 0 ∧ 0 < a₂ ∧ b₁ < b₂ ∧ 0 < b₁) ∨                  -- 1.9
  (b₁ < 0 ∧ 0 < a₁ ∧ 0 < a₂ ∧ 0 < b₂) ∨                   -- 1.10
  (a₁ < 0 ∧ b₁ < 0 ∧ 0 < a₂ ∧ 0 < b₂) ∨                   -- 1.11
  (a₂ < 0 ∧ b₁ < 0 ∧ 0 < a₁ ∧ 0 < b₂ ∧ b₂ < |b₁|) ∨       -- 1.12
  (a₂ < 0 ∧ b₁ < 0 ∧ 0 < a₁ ∧ 0 < b₂ ∧ |b₁| < b₂) ∨       -- 1.13
  (a₂ < 0 ∧ b₁ < 0 ∧ 0 < a₁ ∧ 0 < b₂ ∧ |b₁| = b₂) ∨       -- 1.14
  (b₁ < 0 ∧ b₂ < 0 ∧ 0 < a₁ ∧ 0 < a₂) ∨                   -- 1.15
  (0 < b₁ ∧ 0 < b₂ ∧ a₁ < 0 ∧ a₂ < 0) ∨                   -- 1.16
  (a₁ < 0 ∧ a₂ < 0 ∧ b₁ < 0 ∧ 0 < b₂ ∧ b₂ < |b₁|) ∨       -- 1.17
  (a₁ < 0 ∧ a₂ < 0 ∧ b₁ < 0 ∧ 0 < b₂ ∧ |b₁| < b₂) ∨       -- 1.18
  (a₁ < 0 ∧ a₂ < 0 ∧ b₁ < 0 ∧ 0 < b₂ ∧ |b₁| = b₂) ∨       -- 1.19
  (a₂ < 0 ∧ b₁ < 0 ∧ b₂ < 0 ∧ 0 < a₁ ∧ |b₂| < |b₁|) ∨     -- 1.20
  (a₂ < 0 ∧ b₁ < 0 ∧ b₂ < 0 ∧ 0 < a₁ ∧ |b₁| < |b₂|) ∨     -- 1.21
  (a₂ < 0 ∧ b₁ < 0 ∧ b₂ < 0 ∧ a₁ < 0)                     -- 1.22

/-- **Cases 2.1–2.5 of Theorem EC.1, corrected** (Liu, arXiv:2107.11939v4, pp.ec16–ec17), for
`h(k) = a b^k + c k b^(k−1) + d`.

**Formalization Note.** Correction: `h(⌈z₃⌉)` for the printed `h(z₃ + 1)` in 2.1. The missing `max`
of 2.4 is restored. In 2.5 the forms "similar to those in (1.1)–(1.6)" are written out: for `c = 0`
those of 1.5–1.6 with `(a₁, b₁, c) := (a, b, d)`, and for `b = 0` that of 1.4. -/
structure JordanCases (h : ℕ → ℝ) (r : ℝ) (L : ℕ∞) (a b c d : ℝ) : Prop where
  /-- Case 2.1, (EC.61), corrected: `h(⌈z₃⌉)` for `h(z₃ + 1)`. -/
  case_2_1 : 0 < b → 0 < c →
    (0 < zThree a b c ∧ h 0 ≤ r ∧ r < h ⌈zThree a b c⌉.toNat →
      EqMin L {k : ℕ | 0 ≤ k ∧ (k : ℤ) < ⌈zThree a b c⌉ + 1 ∧ r < h k}) ∧
    ((0 < zThree a b c ∧ h ⌈zThree a b c⌉.toNat ≤ r) ∨ (zThree a b c ≤ 0 ∧ h 0 ≤ r) →
      L = ⊤)
  /-- Case 2.2, (EC.62). -/
  case_2_2 : 0 < b → c < 0 →
    (h 0 ≤ r ∧ r < d →
      EqMin L {k : ℕ | max (⌈zThree a b c⌉ + 1) 0 ≤ (k : ℤ) ∧ r < h k}) ∧
    (max (h 0) d ≤ r → L = ⊤)
  /-- Case 2.3, (EC.63). -/
  case_2_3 : b < 0 → c < 0 →
    (0 < zFour a b c ∧ h 0 ≤ r ∧ r < h (evenFloor (zFour a b c) + 2).toNat →
      EqMin L {k : ℕ | 1 ≤ k ∧ (k : ℤ) ≤ evenFloor (zFour a b c) + 2 ∧ r < h k}) ∧
    ((0 < zFour a b c ∧
          max (max (h 0) (h 1)) (h (evenFloor (zFour a b c) + 2).toNat) ≤ r) ∨
        (zFour a b c ≤ 0 ∧ h 0 ≤ r) →
      L = ⊤)
  /-- Case 2.4, (EC.64), with the missing `max` restored. -/
  case_2_4 : b < 0 → 0 < c →
    (1 < zFour a b c ∧ h 0 ≤ r ∧ r < h (oddFloor (zFour a b c) + 2).toNat →
      EqMin L {k : ℕ | 1 ≤ k ∧ (k : ℤ) ≤ oddFloor (zFour a b c) + 2 ∧ r < h k}) ∧
    ((zFour a b c ≤ 1 ∧ max (h 0) (h 1) ≤ r) ∨
        (1 < zFour a b c ∧
          max (max (h 0) (h 1)) (h (oddFloor (zFour a b c) + 2).toNat) ≤ r) →
      L = ⊤)
  /-- Case 2.5 (`bc = 0`), the forms of 1.4–1.6. -/
  case_2_5 : b * c = 0 →
    (c = 0 → 0 < b → a < 0 →
      (max (h 0) (h 1) ≤ r ∧ r < d → EqInt L (⌊logb b ((d - r) / -a)⌋ + 1)) ∧
      (max (h 0) d ≤ r → L = ⊤)) ∧
    (c = 0 → (b ≤ 0 ∨ 0 ≤ a) → max (max (h 0) (h 1)) (h 2) ≤ r → L = ⊤) ∧
    (b = 0 → max (max (h 0) (h 1)) (h 2) ≤ r → L = ⊤)

/-- **Cases 3.1–3.8 of Theorem EC.1** (Liu, arXiv:2107.11939v4, p.ec17), for
`h(k) = a′ A^k sin(kθ + b′) + c′`, with `d′ = (r* − c′)/a′`.

**Formalization Note.** Used only with `a′ > 0`, where `d′` is defined. In 3.1 "the maximum of
`h(k)` over the finite range exceeds `r*`" is written as an existential and "is at most `r*`" as a
universal statement. In 3.7 and 3.8 the misprinted `b` is `b′`. -/
structure ComplexCases (h : ℕ → ℝ) (r : ℝ) (L : ℕ∞) (a' A θ b' c' : ℝ) : Prop where
  /-- Case 3.1, (EC.65). -/
  case_3_1 : 0 < (r - c') / a' →
    (0 < logb A ((r - c') / a') ∧
        (∃ k : ℕ, (k : ℤ) < ⌈logb A ((r - c') / a')⌉ ∧ r < h k) →
      EqMin L {k : ℕ | 0 ≤ k ∧ (k : ℤ) < ⌈logb A ((r - c') / a')⌉ ∧ r < h k}) ∧
    (logb A ((r - c') / a') ≤ 0 ∨
        (0 < logb A ((r - c') / a') ∧
          ∀ k : ℕ, (k : ℤ) < ⌈logb A ((r - c') / a')⌉ → h k ≤ r) →
      L = ⊤)
  /-- Case 3.2. -/
  case_3_2 : (r - c') / a' < 0 → EqMin L {k : ℕ | 0 ≤ k ∧ r < h k}
  /-- Case 3.3. -/
  case_3_3 : (r - c') / a' = 0 → b' ∈ Set.Ioo 0 π → L = 0
  /-- Case 3.4. -/
  case_3_4 : (r - c') / a' = 0 → θ = π → (b' = 0 ∨ b' = π) → L = ⊤
  /-- Case 3.5. -/
  case_3_5 : (r - c') / a' = 0 → θ ≠ π → b' = 0 → EqInt L (⌊π / (2 * π - θ)⌋ + 1)
  /-- Case 3.6. -/
  case_3_6 : (r - c') / a' = 0 → θ ≠ π → b' = π → EqInt L (⌊π / θ⌋ + 1)
  /-- Case 3.7, with `b′` for the misprinted `b`. -/
  case_3_7 : (r - c') / a' = 0 → θ ∈ Set.Ioc 0 π → b' ∈ Set.Ioo π (2 * π) →
    EqInt L (⌊(2 * π - b') / θ⌋ + 1)
  /-- Case 3.8, with `b′` for the misprinted `b`. -/
  case_3_8 : (r - c') / a' = 0 → θ ∈ Set.Ioo π (2 * π) → b' ∈ Set.Ioo π (2 * π) →
    EqInt L (⌊(b' - π) / (2 * π - θ)⌋ + 1)

end RelaxedIndexability.Supplement


