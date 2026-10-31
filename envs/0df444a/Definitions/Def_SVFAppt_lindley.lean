-- Prove2me | Definitions.Def_SVFAppt_lindley
-- name    : SVFAppt_lindley
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:20:59.25741+00:00
-- url     : https://prove2.me/theorems/1aef1c7c-09dd-4ee3-ad06-c67b18b810a8
-- title:
--   Lindley recursions (1) for waiting and idle times of an appointment sequence
-- statement:
--   A doctor sees $n$ patients one after another. A **sequence** is a permutation $\tau$ of the patients: $\tau(i)$ is the patient in appointment slot $i$. A **schedule** $x=(x_j)_j$ reserves a slot of length $x_j$ for patient $j$ (indexed by patient, not by slot). Given a realization $b=(b_j)_j$ of the service times, the waiting time $W_i$ of the patient in slot $i$ and the idle time $I_i$ of the doctor before slot $i$ satisfy the **Lindley recursions**
--
--   $$W_{i+1}=\big(W_i+b_{\tau(i)}-x_{\tau(i)}\big)^+,\qquad I_{i+1}=\big(W_i+b_{\tau(i)}-x_{\tau(i)}\big)^-,$$
--
--   with $y^+=\max\{0,y\}$ and $y^-=\max\{0,-y\}$, started from $W=I=0$ in the first slot.
--
--   These recursions define every quantity of the mission: the cost (2) is a weighted sum of the expectations of $W_i$ and $I_i$.
--
--   **Formalization Note** Slots are 0-based: Lean slot $i$ is the paper's slot $i+1$, and $W_0=I_0=0$ is the paper's $W_1=I_1=0$ (the convention under which the paper's identity (5) holds). `lindley τ x b i` is the pair $(W_i,I_i)$; `wait` and `idle` are its components. The step is defined for $i<n$ (so $W_n$ is the overtime of Remark 3.7); values at indices beyond $n$ are $0$ and never used.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, §2.1, eq. (1), p. 8

import Mathlib

namespace SVFAppt

/-- **Lindley recursions (1) for the waiting and idle times of an appointment sequence.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, §2.1, eq. (1), p. 8: "Given a sequence τ and
interarrival times xi, the waiting times and idle times satisfy the Lindley recursions
Wi+1 = (Wi + Bτ(i) − xτ(i))+, Ii+1 = (Wi + Bτ(i) − xτ(i))−".

`lindley τ x b i = (W_i, I_i)` for one realization `b : Fin n → ℝ` of the service times
(`b j` is the service time of patient `j`), a sequence `τ` (`τ i` is the patient in slot `i`) and a
schedule `x` (`x j` is the slot length reserved for patient `j`).

**Formalization Note**
* Slots are 0-based: Lean slot `i` is the paper's slot `i + 1`, so `W 0 = I 0 = 0` is the paper's
  `W_1 = I_1 = 0` (the first patient arrives at time 0 to an idle doctor; this is the convention
  under which the paper's identity (5) holds).
* The schedule is indexed by patient, not by slot: slot `i` has length `x (τ i)`.
* The step from slot `i` to slot `i + 1` is defined for `i < n` (so `W_n` is the overtime of
  Remark 3.7); the values at indices `> n` are `(0, 0)` and are never used. -/
noncomputable def lindley {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | i + 1 =>
    if h : i < n then
      (max 0 ((lindley τ x b i).1 + b (τ ⟨i, h⟩) - x (τ ⟨i, h⟩)),
        max 0 (-((lindley τ x b i).1 + b (τ ⟨i, h⟩) - x (τ ⟨i, h⟩))))
    else (0, 0)

/-- The waiting time `W_i` of the patient in (0-based) appointment slot `i`, from the Lindley
recursion (1) (arXiv:1812.01467v4, p. 8). See `lindley` for the conventions. -/
noncomputable def wait {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) (i : ℕ) : ℝ :=
  (lindley τ x b i).1

/-- The idle time `I_i` of the doctor before the start of (0-based) appointment slot `i`, from the
Lindley recursion (1) (arXiv:1812.01467v4, p. 8). See `lindley` for the conventions. -/
noncomputable def idle {n : ℕ} (τ : Equiv.Perm (Fin n)) (x b : Fin n → ℝ) (i : ℕ) : ℝ :=
  (lindley τ x b i).2

end SVFAppt


