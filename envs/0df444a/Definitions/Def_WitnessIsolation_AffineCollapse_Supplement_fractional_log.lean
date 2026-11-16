-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_fractional_log
-- name    : WitnessIsolation_AffineCollapse_Supplement_fractional_log
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:57.492822+00:00
-- url     : https://prove2.me/theorems/fb4aedbe-cc3b-45a6-8898-ab68908d97d8
-- title:
--   Fractional iterates of the logarithm
-- statement:
--   All logarithms are base two. Let $E_0(u)=u$ and $E_{m+1}(u)=2^{E_m(u)}$. Every $x\ge2$ is uniquely $x=E_m(u)$ with $m\ge0$ and $2\le u<4$; put
--   $$A(x)=m+\frac{u-2}{2}.$$
--   Here $m$ is the least $m$ with $x<E_m(4)$ and $u=\log^{(m)}x$ is the $m$-fold iterated logarithm. On $[0,\infty)$ the inverse is $A^{-1}(y)=E_{\lfloor y\rfloor}\bigl(2+2(y-\lfloor y\rfloor)\bigr)$. For an integer $q\ge1$ and $x\ge2$ with $A(x)\ge1/q$,
--   $$R_q(x)=A^{-1}\bigl(A(x)-1/q\bigr),$$
--   and the rate of Theorem 7.3 is $c/R_q(n)^a$.
--
--   $R_q$ is the source's fractional iterate of the logarithm. Its stated properties ($R_1=\log$, $R_q^{\circ q}=\log$, $R_q(\log x)=\log R_q(x)$, and Lemma 7.2) are theorem clauses of `fractional_log_properties`, not assumptions.
--
--   **Formalization Note** Lean needs total functions. Outside the source's domain the extensions are arbitrary: $A(x)=0$ for $x<2$, $A^{-1}(y)=2$ for $y<0$, and $R_q(x)=2$ when $q=0$, $x<2$ or $A(x)<1/q$. Every statement that uses $R_q$ is eventual, so these values do not enter any assertion. The tower stage of an $x<2$ is assigned $0$; existence of the stage for $x\ge2$ is a proof obligation.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 13, PDF p. 14, §7.1 (definition of E_m, A and R_q, before Lemma 7.2)

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

def tower : ℕ → ℝ → ℝ
  | 0, u => u
  | m+1, u => (2:ℝ) ^ tower m u

def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | m+1, x => Real.logb 2 (iterLog m x)

/-- Least tower interval. The impossible empty case is assigned stage zero;
existence on x≥2 is a proof obligation in fractional_log_properties. -/
def towerStage (x : ℝ) : ℕ := by
  classical
  exact if h : ∃ m : ℕ, x < tower m 4 then Nat.find h else 0

def abelCoordinate (x : ℝ) : ℝ :=
  if 2 ≤ x then (towerStage x : ℝ) + (iterLog (towerStage x) x - 2)/2 else 0

/-- Explicit inverse on [0,∞); the arbitrary extension on negatives is 2. -/
def abelInverse (y : ℝ) : ℝ :=
  if 0 ≤ y then tower ⌊y⌋₊ (2 + 2*(y - (⌊y⌋₊:ℝ))) else 2

/-- The specified Abel-coordinate root, not an arbitrary compositional root.
Outside q≥1 and A(x)≥1/q we fix the total extension to 2. -/
def fractionalLog (q : ℕ) (x : ℝ) : ℝ :=
  if 1 ≤ q ∧ 2 ≤ x ∧ 1/(q:ℝ) ≤ abelCoordinate x then
    abelInverse (abelCoordinate x - 1/(q:ℝ)) else 2

def fractionalRate (q : ℕ) (a c : ℝ) (n : ℕ) : ℝ :=
  c / (fractionalLog q (n:ℝ)) ^ a

end WitnessIsolation.AffineCollapse.Supplement


