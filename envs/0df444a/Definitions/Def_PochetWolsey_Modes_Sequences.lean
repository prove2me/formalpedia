-- Prove2me | Definitions.Def_PochetWolsey_Modes_Sequences
-- name    : PochetWolsey_Modes_Sequences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:02.568822+00:00
-- url     : https://prove2.me/theorems/0cf57a4e-7b9a-4303-9acc-40ec046ed05e
-- title:
--   Ordered setup sequences with startups and switch-offs
-- statement:
--   A schedule assigns each period a nonempty list of distinct item labels. The final label in each period equals the first label in the following period. Define $y_i(t)$ as membership in the list, $z_i(t)$ as membership after its first position, and $w_i(t)$ as membership before its last position. Thus
--   $$y_i(t)-z_i(t)=\mathbf1\{i\text{ is first in period }t\},\qquad y_i(t)-w_i(t)=\mathbf1\{i\text{ is last in period }t\}.$$
--   The arbitrary-count mode set consists of all resulting triples $(y,z,w)$. The two-mode set consists of the pairs $(y,z)$ arising from lists of length at most two. A separate binary constraint system imposes $\sum_i(y_i(t)-z_i(t))=1$, $\sum_i z_i(t)\le1$, $z_i(t)\le y_i(t)$ and, for adjacent periods,
--   $$z_i(t+1)\ge y_i(t+1)-y_i(t),\qquad z_i(t+1)+z_i(t)\le y_i(t+1).$$
--   The list model encodes the physical sequence independently of the proposed polyhedra. First and last labels are unrestricted; the first label is carried in and the last is carried out.
--
--   **Formalization Note** There are $m+1$ labels, including idle label $0$, and $n+1$ periods, numbered $0,\ldots,n$. Thus $m=n=0$ means one idle label and one period, not empty index sets. The unspecified pre-horizon state in Proposition 12.5 is existentially eliminated: take its setup to be the first label and its startup zero. Consequently the two inequalities involving a previous period are imposed only on adjacent modeled periods, while $z\le y$ holds in every period.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 379 (PDF 390), Section 12.3, pp. 378–381; Proposition 12.5

import Mathlib

namespace PochetWolsey.Modes

abbrev Schedule (m n : ℕ) := Fin (n + 1) → List ((Fin (m + 1)))
abbrev ModePoint (m n : ℕ) := (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ)

/-- Nonempty, repetition-free period lists with last-to-first continuity. -/
def ValidSchedule {m n : ℕ} (s : Schedule m n) : Prop :=
  (∀ t, s t ≠ [] ∧ (s t).Nodup) ∧
  (∀ t : Fin n, (s t.castSucc).getLast? = (s t.succ).head?)

def setupVector {m n : ℕ} (s : Schedule m n) : (Fin (m + 1) → Fin (n + 1) → ℝ) :=
  fun i t => if i ∈ s t then 1 else 0

def startupVector {m n : ℕ} (s : Schedule m n) : (Fin (m + 1) → Fin (n + 1) → ℝ) :=
  fun i t => if i ∈ (s t).tail then 1 else 0

def switchoffVector {m n : ℕ} (s : Schedule m n) : (Fin (m + 1) → Fin (n + 1) → ℝ) :=
  fun i t => if i ∈ (s t).dropLast then 1 else 0

def modeVector {m n : ℕ} (s : Schedule m n) : ModePoint m n :=
  (setupVector s, startupVector s, switchoffVector s)

def arbitraryModeSet (m n : ℕ) : Set (ModePoint m n) :=
  {p | ∃ s : Schedule m n, ValidSchedule s ∧ p = modeVector s}

def twoModeSet (m n : ℕ) : Set ((Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ)) :=
  {p | ∃ s : Schedule m n, ValidSchedule s ∧ (∀ t, (s t).length ≤ 2) ∧
    p = (setupVector s, startupVector s)}

/-- Proposition 12.5 with the unspecified initial state eliminated. -/
def twoModeBinarySystem (m n : ℕ) : Set ((Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ)) :=
  {p | (∀ i, (∀ t, p.1 i t = 0 ∨ p.1 i t = 1)) ∧ (∀ i, (∀ t, p.2 i t = 0 ∨ p.2 i t = 1)) ∧
    (∀ t, ∑ i, (p.1 i t - p.2 i t) = 1) ∧
    (∀ t, ∑ i, p.2 i t ≤ 1) ∧
    (∀ i t, p.2 i t ≤ p.1 i t) ∧
    (∀ i (t : Fin n), p.2 i t.succ ≥ p.1 i t.succ - p.1 i t.castSucc) ∧
    (∀ i (t : Fin n), p.2 i t.succ + p.2 i t.castSucc ≤ p.1 i t.succ)}

end PochetWolsey.Modes


