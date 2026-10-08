-- Prove2me | Definitions.Def_SpeedScaling_AVR_Example2
-- name    : SpeedScaling_AVR_Example2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:09.851992+00:00
-- url     : https://prove2.me/theorems/4536847d-781d-4306-b0b6-594761aa0bd7
-- title:
--   The variable-exponent family from Example 2
-- statement:
--   For each exponent $e$ and positive integer $n$, job $i=1,\ldots,n$ has window $[0,i/n]$ and density $(n/i)^e$. The instance therefore has requirement $R_i=(i/n)(n/i)^e$. The slot schedule runs job $i$ on $((i-1)/n,i/n)$ at speed $n(n/i)^{e-1}$ and has zero speed on slot boundaries.
--
--   The exponent $3/2$ specialization witnesses the lower bound of Theorem 2. Lean's index $i\in\operatorname{Fin}(n)$ denotes paper job $i+1$.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 376, Example 2.

import Definitions.Def_SpeedScaling_AVR_Model

namespace SpeedScaling.AVR
noncomputable section
open scoped Classical

/-- Example 2 with exponent `e`; Lean index `i` denotes paper job `i+1`. -/
def ex2InstancePower (e : ℝ) (n : ℕ) (hn : 0 < n) : Instance n where
  t0 := 0
  t1 := 1
  ht := by norm_num
  a := fun _ => 0
  b := fun i => ((i : ℕ) + 1 : ℝ) / n
  R := fun i => (((i : ℕ) + 1 : ℝ) / n) * ((n : ℝ) / ((i : ℕ) + 1)) ^ e
  ha := by intro i; exact le_refl _
  hab := by
    intro i
    positivity
  hb := by
    intro i
    have hnum : ((i : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast i.isLt
    exact (div_le_one (by exact_mod_cast hn)).2 hnum
  hR := by intro i; positivity

/-- The unique open slot containing `t`, if there is one. -/
def ex2Index (n : ℕ) (t : ℝ) : Option (Fin n) :=
  if h : ∃ i : Fin n, t ∈ Set.Ioo ((i : ℝ) / n) (((i : ℝ) + 1) / n)
    then some (Classical.choose h) else none

/-- The slot schedule described after Example 2, zero at slot boundaries. -/
def ex2SchedulePower (e : ℝ) (n : ℕ) (_hn : 0 < n) : Schedule n where
  job := ex2Index n
  s := fun t => match ex2Index n t with
    | none => 0
    | some i => (n : ℝ) * ((n : ℝ) / ((i : ℝ) + 1)) ^ (e - 1)

/-- The exponent giving the limiting ratio four. -/
def ex2Instance (n : ℕ) (hn : 0 < n) : Instance n :=
  ex2InstancePower (3 / 2 : ℝ) n hn

/-- The corresponding slot schedule. -/
def ex2Schedule (n : ℕ) (hn : 0 < n) : Schedule n :=
  ex2SchedulePower (3 / 2 : ℝ) n hn

end
end SpeedScaling.AVR


