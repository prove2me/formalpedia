-- Prove2me | Definitions.Def_PrivLearn_Generic_ExpMech
-- name    : PrivLearn_Generic_ExpMech
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:15.283989+00:00
-- url     : https://prove2.me/theorems/79972739-7433-4c71-b3a4-0b2fff5df074
-- title:
--   Error, OPT, training error, the score q(z, h) and the exponential mechanism A^ε_q
-- statement:
--   Fix a set $X$ of examples and labels $\{0,1\}$. A **hypothesis** is a function $h:X\to\{0,1\}$, and a **distribution on labeled examples** is a probability measure $P$ on $X\times\{0,1\}$.
--
--   1. The **error** of $h$ on $P$ (§2.2, p. 9) is $\mathrm{err}(h)=\Pr_{(x,y)\sim P}[h(x)\neq y]$.
--   2. For a finite nonempty class $H$ of hypotheses, $\mathrm{OPT}=\min_{f\in H}\mathrm{err}(f)$ (Definition 2.5, p. 10, with $H=C_d$).
--   3. For a database $z=((x_1,y_1),\dots,(x_n,y_n))$ of labeled examples, the **score** of $h$ is $q(z,h)=-|\{i: y_i\neq h(x_i)\}|$, minus the number of examples $h$ misclassifies, and the **training error** is $\mathrm{err}_T(h)=|\{i\in[n]: h(x_i)\neq y_i\}|/n=-q(z,h)/n$ (p. 11).
--   4. The **exponential mechanism** $\mathcal A^{\varepsilon}_q$ (p. 11) outputs, on input $z$, a hypothesis $h\in H$ with probability proportional to $\exp(\varepsilon q(z,h)/2)$:
--
--   $$\Pr[\mathcal A^{\varepsilon}_q(z)=h]=\frac{\exp(\varepsilon q(z,h)/2)}{\sum_{h'\in H}\exp(\varepsilon q(z,h')/2)},\qquad h\in H.$$
--
--   These are the objects of the generic private learner: the mechanism prefers hypotheses with few training mistakes, and its analysis compares training error with true error.
--
--   **Formalization Note.** $\mathcal A^{\varepsilon}_q(z)$ is defined as the measure $\sum_{h\in H} p_z(h)\,\delta_h$ on the function space `X → Bool` with the product σ-algebra; it has total mass $1$ whenever $H$ is nonempty (every weight is positive), which the theorems assume and a solver proves, it is not built into the definition. For $n=0$, Lean's convention $0/0=0$ makes $\mathrm{err}_T\equiv0$; the paper never uses $n=0$. `err` is the real number $P(\{(x,y):h(x)\neq y\})$; the database is indexed from $0$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 9 (err), p. 10 (Definition 2.5, OPT), p. 11 (score q, A^ε_q, err_T in the proof of Theorem 3.4)

import Mathlib

namespace PrivLearn.Generic

open MeasureTheory

variable {X : Type*}

/-- §2.2 (p. 9): the misclassification error `err(h) = Pr_{(x,y)∼D}[h(x) ≠ y]` of the hypothesis
`h : X → {0,1}` on the distribution `P` of labeled examples (agnostic setting). -/
noncomputable def err [MeasurableSpace X] (P : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  (P {p | h p.1 ≠ p.2}).toReal

/-- Definition 2.5 (p. 10): `OPT = min_{f ∈ H} err(f)`, the least error of a hypothesis of the
finite nonempty class `H` (Theorem 3.4 takes `H_d = C_d`). -/
noncomputable def OPT [MeasurableSpace X] (P : Measure (X × Bool)) (H : Finset (X → Bool))
    (hH : H.Nonempty) : ℝ :=
  H.inf' hH (err P)

/-- p. 11: the score `q(z, h) = −|{i : y_i ≠ h(x_i)}|`, minus the number of examples of the
database `z = ((x_1, y_1), …, (x_n, y_n))` misclassified by `h`. -/
def score {n : ℕ} (z : Fin n → X × Bool) (h : X → Bool) : ℝ :=
  -((Finset.univ.filter fun i => h (z i).1 ≠ (z i).2).card : ℝ)

/-- Proof of Theorem 3.4 (p. 11): the training error
`err_T(h) = |{i ∈ [n] | h(x_i) ≠ y_i}| / n = −q(z, h)/n`. -/
noncomputable def errT {n : ℕ} (z : Fin n → X × Bool) (h : X → Bool) : ℝ :=
  ((Finset.univ.filter fun i => h (z i).1 ≠ (z i).2).card : ℝ) / n

/-- The unnormalised weight `exp(ε q(z, h) / 2)` of the hypothesis `h` in `A^ε_q(z)` (p. 11). -/
noncomputable def weight (ε : ℝ) {n : ℕ} (z : Fin n → X × Bool) (h : X → Bool) : ℝ :=
  Real.exp (ε * score z h / 2)

/-- The exponential mechanism `A^ε_q` (p. 11): on the database `z`, "output hypothesis `h ∈ H`
with probability proportional to `exp(ε q(z, h)/2)`". This is the law of its output, a measure on
hypotheses `X → Bool` (product σ-algebra). -/
noncomputable def expMech (H : Finset (X → Bool)) (ε : ℝ) {n : ℕ} (z : Fin n → X × Bool) :
    Measure (X → Bool) :=
  ∑ h ∈ H, ENNReal.ofReal (weight ε z h / ∑ h' ∈ H, weight ε z h') • Measure.dirac h

end PrivLearn.Generic


