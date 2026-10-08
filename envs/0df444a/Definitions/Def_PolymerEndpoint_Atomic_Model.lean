-- Prove2me | Definitions.Def_PolymerEndpoint_Atomic_Model
-- name    : PolymerEndpoint_Atomic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:32.853019+00:00
-- url     : https://prove2.me/theorems/c8c3d5bf-2d8b-4f68-abb7-60beea352809
-- title:
--   Directed polymer model, endpoint distribution, and temperature phases
-- statement:
--   Fix an integer $d\geq1$. A polymer path makes one of the $2d$ nearest-neighbor steps at each time, starting at the origin in $\mathbb Z^d$. The environment $X_{i,x}$ is an independent, identically distributed family of real random variables with common law $\mathfrak L$; only times $i\geq1$ enter the path energy. The path weight is the exponential of $\beta$ times the sum of the environment along the path. The partition function $Z_n$ is the mean of these weights over all $(2d)^n$ paths, and $f_n(x)$ is the fraction of total weight carried by paths ending at $x$. The free energy is $F_n=\log Z_n/n$, with $F_0=0$.
--
--   The disorder law is nondegenerate and satisfies the exponential-moment condition
--   $$
--   \lambda(\alpha)=\log\mathbb E_{\mathfrak L}e^{\alpha X}<\infty\quad(-2\beta\leq\alpha\leq2\beta).
--   $$
--   The low-temperature phase means that the limit of the averaged free energy is strictly below $\lambda(\beta)$; the high-temperature phase means the two are equal. For $\varepsilon>0$, the atom mass is the total endpoint probability at sites where $f_n(x)>\varepsilon$.
--
--   **Formalization Note** The environment has a harmless unused time-zero row. The phase is encoded by the limiting characterization in Theorem A, rather than by a separately chosen value of $\beta_c$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, pp. 4–5, §1.1 and Theorem A; p. 9, §1.2.3; p. 26, (3.1); p. 42, §6.1

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

abbrev Cell (d : ℕ) := ℕ × (Fin d → ℤ)
abbrev Step (d : ℕ) := Fin d × Bool

def l1 {d : ℕ} (x : Fin d → ℤ) : ℕ := ∑ j, (x j).natAbs

def stepVec {d : ℕ} (s : Step d) : Fin d → ℤ :=
  Pi.single s.1 (if s.2 then 1 else -1)

def pos {d n : ℕ} (s : Fin n → Step d) (i : ℕ) : Fin d → ℤ :=
  ∑ j : Fin n, if (j : ℕ) < i then stepVec (s j) else 0

def IsEnvironment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Cell d → Ω → ℝ) (𝔏 : Measure ℝ) (P : Measure Ω) : Prop :=
  (∀ u, Measurable (X u)) ∧ iIndepFun X P ∧ ∀ u, P.map (X u) = 𝔏

def Nondegenerate (𝔏 : Measure ℝ) : Prop :=
  ∀ c : ℝ, 𝔏 ≠ Measure.dirac c

def MomentCondition (𝔏 : Measure ℝ) (β : ℝ) : Prop :=
  ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x : ℝ => Real.exp (α * x)) 𝔏

noncomputable def logMGF (𝔏 : Measure ℝ) (α : ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (α * x) ∂𝔏)

noncomputable def weight {d n : ℕ} {Ω : Type*} (X : Cell d → Ω → ℝ)
    (β : ℝ) (s : Fin n → Step d) (a : Ω) : ℝ :=
  Real.exp (β * ∑ m : Fin n, X ((m : ℕ) + 1, pos s ((m : ℕ) + 1)) a)

noncomputable def Z {d : ℕ} {Ω : Type*} (X : Cell d → Ω → ℝ)
    (β : ℝ) (n : ℕ) (a : Ω) : ℝ :=
  ((2 * d : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Step d, weight X β s a

noncomputable def endpt {d : ℕ} {Ω : Type*} (X : Cell d → Ω → ℝ)
    (β : ℝ) (n : ℕ) (a : Ω) (x : Fin d → ℤ) : ℝ :=
  (∑ s : Fin n → Step d, if pos s n = x then weight X β s a else 0) /
    (∑ s : Fin n → Step d, weight X β s a)

noncomputable def F {d : ℕ} {Ω : Type*} (X : Cell d → Ω → ℝ)
    (β : ℝ) (n : ℕ) (a : Ω) : ℝ := Real.log (Z X β n a) / n

noncomputable def envLaw {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] :
    Measure (Cell d → ℝ) := Measure.infinitePi (fun _ => 𝔏)

noncomputable def meanF {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (β : ℝ) (n : ℕ) : ℝ :=
  ∫ Y, F (fun u Y => Y u) β n Y ∂(envLaw (d := d) 𝔏)

def LowTemp {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Prop :=
  ∃ p : ℝ, p < logMGF 𝔏 β ∧ Tendsto (meanF (d := d) 𝔏 β) atTop (𝓝 p)

def HighTemp {d : ℕ} (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏] (β : ℝ) : Prop :=
  Tendsto (meanF (d := d) 𝔏 β) atTop (𝓝 (logMGF 𝔏 β))

noncomputable def atomMass {d : ℕ} {Ω : Type*} (X : Cell d → Ω → ℝ)
    (β : ℝ) (n : ℕ) (ε : ℝ) (a : Ω) : ℝ :=
  (∑ s : Fin n → Step d,
      weight X β s a * if ε < endpt X β n a (pos s n) then 1 else 0) /
    (∑ s : Fin n → Step d, weight X β s a)

end PolymerEndpoint.Atomic


