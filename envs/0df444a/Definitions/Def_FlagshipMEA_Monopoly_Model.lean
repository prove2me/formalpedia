-- Prove2me | Definitions.Def_FlagshipMEA_Monopoly_Model
-- name    : FlagshipMEA_Monopoly_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:55.37177+00:00
-- url     : https://prove2.me/theorems/33d0ba00-6e25-40bd-ada8-eb2e71f00e3b
-- title:
--   §2, equations (7)–(9) and Definitions 1–2 — monopoly marketing effort model
-- statement:
--   A firm offers a finite line of products. Product $i$ has base utility $u_i$ and positive markup $\pi_i$; consumers have logit taste scale $\lambda>0$, and the outside option has attraction $1$. The firm chooses a utility increase $\Delta u_i\geq\theta$ at cost $c(\Delta u_i)$. Equation (7) changes coordinates to the nonnegative **multiplier** $m_i=e^{\Delta u_i/\lambda}-e^{\theta/\lambda}$. An allocation is feasible when every $m_i\geq0$; its total marketing effort is $M=\sum_i m_i$.
--
--   The firm's revenue, cost, and profit in equation (8) are
--
--   $$\operatorname{rev}(m)=\frac{\sum_i(m_i+e^{\theta/\lambda})e^{u_i/\lambda}\pi_i}{1+\sum_i(m_i+e^{\theta/\lambda})e^{u_i/\lambda}},\qquad C(m)=\sum_i c\!\left(\lambda\log(m_i+e^{\theta/\lambda})\right),\qquad P(m)=\operatorname{rev}(m)-C(m).$$
--
--   An optimal allocation maximizes $P$ over all feasible allocations. Definition 1 calls an allocation concentrated when exactly one multiplier is positive. Definition 2 defines the **MEA index** $R_i(M)=A_i(M)/B_i(M)$ for $M>0$, with $A_i(M)$ and $B_i(M)$ given by equation (9). The transformed cost is $f_c(v)=c(\lambda\log v)$.
--
--   These definitions provide the common model for Proposition 1 and its supporting results. **Formalization Note** Products use the zero-based type `Fin n`. The standing assumptions on $c$ are imposed on the feasible range $[\theta,\infty)$, and concavity of $f_c$ on $[e^{\theta/\lambda},\infty)$. Values of $R_i(0)$ and $f_c(v)$ for $v\leq0$ are outside the mathematical domain of their stated uses.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), pp. 7–13 (PDF 9–15), §2, eqs. (7)–(9), Definitions 1–2

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_LogitChoice

namespace FlagshipMEA.Monopoly

/-- The finite product line, its utilities and markups, taste scale, effort floor and cost. -/
structure Data (n : ℕ) where
  u : Fin n → ℝ
  markup : Fin n → ℝ
  lam : ℝ
  θ : ℝ
  c : ℝ → ℝ

/-- Standing assumptions of §2, imposed where feasible utility increases lie. -/
def Data.Standing {n : ℕ} (D : Data n) : Prop :=
  0 < D.lam ∧ (∀ i, 0 < D.markup i) ∧
  StrictMonoOn D.c (Set.Ici D.θ) ∧
  ConvexOn ℝ (Set.Ici D.θ) D.c ∧
  ContDiffOn ℝ 1 D.c (Set.Ici D.θ)

/-- Equation (7), the multiplier attached to a utility increase. -/
noncomputable def Data.multiplier {n : ℕ} (D : Data n) (Δu : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (Δu i / D.lam) - Real.exp (D.θ / D.lam)

noncomputable def Data.base {n : ℕ} (D : Data n) : ℝ := Real.exp (D.θ / D.lam)

/-- Footnote 10: the transformed cost. -/
noncomputable def Data.fc {n : ℕ} (D : Data n) (v : ℝ) : ℝ :=
  D.c (D.lam * Real.log v)

def Data.FcConcave {n : ℕ} (D : Data n) : Prop :=
  ConcaveOn ℝ (Set.Ici D.base) D.fc

def Feasible {n : ℕ} (m : Fin n → ℝ) : Prop := ∀ i, 0 ≤ m i

/-- Product attraction after the marketing allocation, from (3) and (7). -/
noncomputable def Data.attraction {n : ℕ} (D : Data n) (m : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (m i + D.base) * Real.exp (D.u i / D.lam)

/-- The revenue term of (8), including the outside option of attraction 1. -/
noncomputable def Data.revenue {n : ℕ} (D : Data n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, D.markup i * logitShare (D.attraction m) i

noncomputable def Data.cost {n : ℕ} (D : Data n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, D.c (D.lam * Real.log (m i + D.base))

/-- The objective in (8), maximized over every nonnegative allocation. -/
noncomputable def Data.profit {n : ℕ} (D : Data n) (m : Fin n → ℝ) : ℝ :=
  D.revenue m - D.cost m

def Data.IsOptimal {n : ℕ} (D : Data n) (m : Fin n → ℝ) : Prop :=
  Feasible m ∧ ∀ m', Feasible m' → D.profit m' ≤ D.profit m

/-- Definition 1, which excludes the zero allocation. -/
def IsConcentrated {n : ℕ} (m : Fin n → ℝ) : Prop :=
  ∃ i, 0 < m i ∧ ∀ j, j ≠ i → m j = 0

noncomputable def tme {n : ℕ} (m : Fin n → ℝ) : ℝ := ∑ i, m i

/-- Numerator of Definition 2's MEA index, for positive total effort. -/
noncomputable def Data.A {n : ℕ} (D : Data n) (i : Fin n) (m : ℝ) : ℝ :=
  Real.exp (D.u i / D.lam) * D.markup i +
    (1 / m) * (∑ j, Real.exp ((D.u j + D.θ) / D.lam) * D.markup j)

/-- Denominator of Definition 2's MEA index, for positive total effort. -/
noncomputable def Data.B {n : ℕ} (D : Data n) (i : Fin n) (m : ℝ) : ℝ :=
  Real.exp (D.u i / D.lam) +
    (1 / m) * (∑ j, Real.exp ((D.u j + D.θ) / D.lam)) + 1 / m

noncomputable def Data.R {n : ℕ} (D : Data n) (i : Fin n) (m : ℝ) : ℝ :=
  D.A i m / D.B i m

def Data.IsArgmaxR {n : ℕ} (D : Data n) (m : ℝ) (i : Fin n) : Prop :=
  ∀ j, D.R j m ≤ D.R i m

def Data.Distinct {n : ℕ} (D : Data n) : Prop :=
  Function.Injective (fun i => (D.u i, D.markup i))

end FlagshipMEA.Monopoly


