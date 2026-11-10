-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_Instance
-- name    : RealPinwheel_FiveSixths_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:34:32.022972+00:00
-- url     : https://prove2.me/theorems/ca4b521b-5005-4220-8f0c-c8bfd1d1d3e2
-- title:
--   Real-period instances, exact window validity, density and potential
-- statement:
--   A real-period instance is a nonempty ordered tuple $A=(a_1,\ldots,a_n)$ with $1\le a_1\le\cdots\le a_n$, where every $a_i$ is an arbitrary real number. Equal period values still denote different tasks. A schedule $S$ assigns exactly one task to each day. Write $C_i(S;m,h)$ for the number of executions of task $i$ in the half-open block $[m,m+h)$. The schedule is valid precisely when
--
--   $$\forall i,\ \forall\ell\ge1,\ \forall m\ge0,\qquad C_i(S;m,\lceil\ell a_i\rceil)\ge\ell.$$
--
--   Schedulability means existence of such a schedule. A positive integer $L$ is a period when $S(t+L)=S(t)$ for every day $t$. Define density and potential by
--
--   $$D(A)=\sum_{i=1}^n\frac1{a_i},\qquad P(A)=\sum_{i=1}^{n-1}\frac1{a_i}.$$
--
--   Potential is zero for one task. These definitions separate the physical window condition from the sufficient density and potential bounds used in the theorems.
--
--   **Formalization Note** Day zero represents the paper's day one, and `Fin n` labels positions. Raw validity accepts any labelled period vector, so a replacement can retain labels without imposing sortedness. Only the instance structure imposes the source ordering. Natural ceiling equals the ordinary integer ceiling here because the arguments are positive. No schedulability, certificate or coverage property is an instance field.
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Section 1, printed pp. 1–3 (PDF pp. 2–4)

import Mathlib

namespace RealPinwheel.FiveSixths

/-- A source instance: nonempty, real periods at least one, in increasing order. -/
structure Instance (n : ℕ) where
  positive_dimension : 0 < n
  period : Fin n → ℝ
  one_le : ∀ i, 1 ≤ period i
  ordered : Monotone period

/-- Number of executions in the half-open window [m,m+h). -/
def windowCount {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m h : ℕ) : ℕ :=
  ((Finset.range h).filter fun t => S (m + t) = i).card

/-- Raw validity does not require any ordering of the labelled periods.
Day 0 here represents day 1 of the paper. Every positive multiplicity is required. -/
def Valid {n : ℕ} (a : Fin n → ℝ) (S : ℕ → Fin n) : Prop :=
  ∀ (i : Fin n) (ell : ℕ), 0 < ell → ∀ m : ℕ,
    ell ≤ windowCount S i m ⌈(ell : ℝ) * a i⌉₊

def Schedulable {n : ℕ} (a : Fin n → ℝ) : Prop :=
  ∃ S : ℕ → Fin n, Valid a S

def Periodic {n : ℕ} (S : ℕ → Fin n) (L : ℕ) : Prop :=
  0 < L ∧ ∀ t : ℕ, S (t + L) = S t

noncomputable def density {n : ℕ} (A : Instance n) : ℝ :=
  ∑ i, 1 / A.period i

/-- Omit the last position, including when several periods are equal. -/
noncomputable def potential {n : ℕ} (A : Instance n) : ℝ :=
  ∑ i : Fin n, if i.val + 1 < n then 1 / A.period i else 0

end RealPinwheel.FiveSixths


