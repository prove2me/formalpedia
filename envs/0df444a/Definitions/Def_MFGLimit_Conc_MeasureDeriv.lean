-- Prove2me | Definitions.Def_MFGLimit_Conc_MeasureDeriv
-- name    : MFGLimit_Conc_MeasureDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:10.129322+00:00
-- url     : https://prove2.me/theorems/8255ab01-6473-4233-a76d-4ab8854082f8
-- title:
--   §2.2, pp. 5–6 — normalized flat and intrinsic derivatives on Wasserstein space
-- statement:
--   Let $V$ be a real-valued function on $\mathcal P_q(\mathbb R^d)$. A normalized **flat derivative** $\delta V/\delta m$ is jointly continuous in the $W_q$ topology and in the spatial variable, has the prescribed growth on each $W_q$-compact set, integrates to zero against its base measure, and satisfies
--   $$V(m')-V(m)=\int_0^1\left[\int \frac{\delta V}{\delta m}((1-t)m+tm',z)\,m'(dz)-\int \frac{\delta V}{\delta m}((1-t)m+tm',z)\,m(dz)\right]dt.$$
--   Its **intrinsic derivative** is the genuine spatial gradient $D_mV(m,z)=D_z(\delta V/\delta m)(m,z)$. The mixed second intrinsic derivative is taken from a second normalized flat derivative.
--
--   This interface gives the master equation its intended derivatives with respect to a law.
--
--   **Formalization Note** Compactness is sequential compactness for $W_q$, and the displayed integrals are required to be integrable so that Lean's default value for a non-integrable Bochner integral cannot alter the definition. The normalized flat derivatives are witnesses; spatial derivatives are Fréchet derivatives, not free fields.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 5–6, §2.2, (2.2)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Model

namespace MFGLimit.Conc

open MeasureTheory Filter
open scoped ENNReal NNReal

/-- The real value of the Wasserstein metric on the finite-moment domain. -/
noncomputable def Wp {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (p : ℝ) (m m' : Measure α) : ℝ :=
  (WassersteinDRO.Duality.wassersteinDistance p m m').toReal

/-- Sequential compactness in the `W_q` metric on `P_q`, equivalent to compactness there. -/
def IsWqCompact {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (q : ℝ) (K : Set (Measure α)) : Prop :=
  (∀ m ∈ K, IsPp q m) ∧
  ∀ u : ℕ → Measure α, (∀ j, u j ∈ K) →
    ∃ m ∈ K, ∃ r : ℕ → ℕ, StrictMono r ∧
      Tendsto (fun j => Wp q (u (r j)) m) atTop (nhds 0)

/-- Joint continuity of a flat derivative on `P_q × E`, using the Wasserstein metric. -/
def IsWqContinuous {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (q : ℝ) (D : Measure α → α → ℝ) : Prop :=
  ∀ m : Measure α, IsPp q m → ∀ v : α, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ m' : Measure α, IsPp q m' → ∀ v' : α,
      Wp q m m' + dist v v' < δ → |D m v - D m' v'| < ε

/-- The probability mixture `(1-t)m+tm'` in (2.2), for `0 ≤ t ≤ 1`. -/
noncomputable def mixMeasure {α : Type*} [MeasurableSpace α]
    (m m' : Measure α) (t : ℝ) : Measure α :=
  ENNReal.ofReal (1 - t) • m + ENNReal.ofReal t • m'

/-- A normalized flat derivative of `V` on `P_q`, literally satisfying (2.2). The
integrability clauses make every displayed integral an actual integral. -/
def IsFlatDeriv {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α]
    (q : ℝ) (V : Measure α → ℝ) (D : Measure α → α → ℝ) : Prop :=
  IsWqContinuous q D ∧
  (∀ K : Set (Measure α), IsWqCompact q K →
    ∃ c : ℝ, ∀ m ∈ K, ∀ v : α, |D m v| ≤ c * (1 + ‖v‖ ^ q)) ∧
  (∀ m : Measure α, IsPp q m →
    Integrable (D m) m ∧ ∫ v, D m v ∂m = 0) ∧
  (∀ m m' : Measure α, IsPp q m → IsPp q m' →
    (∀ t : ℝ, t ∈ Set.Icc 0 1 →
      Integrable (D (mixMeasure m m' t)) m ∧
      Integrable (D (mixMeasure m m' t)) m') ∧
    IntegrableOn (fun t : ℝ =>
      (∫ v, D (mixMeasure m m' t) v ∂m') -
      (∫ v, D (mixMeasure m m' t) v ∂m)) (Set.Icc (0 : ℝ) 1) ∧
    V m' - V m = ∫ t in Set.Icc (0 : ℝ) 1,
      ((∫ v, D (mixMeasure m m' t) v ∂m') -
       (∫ v, D (mixMeasure m m' t) v ∂m)))

/-- The intrinsic derivative is the genuine Fréchet gradient in the state variable. -/
noncomputable def grad {d : ℕ} (F : E d → ℝ) (x : E d) : E d :=
  (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ F x)

/-- Intrinsic first derivative obtained from a flat-derivative witness. -/
noncomputable def intrinsicDeriv {d : ℕ}
    (D : Measure (E d) → E d → ℝ) (m : Measure (E d)) (v : E d) : E d :=
  grad (D m) v

/-- The mixed intrinsic second derivative, from the normalized second flat derivative. -/
noncomputable def intrinsicSecond {d : ℕ}
    (D₂ : Measure (E d) → E d → E d → ℝ)
    (m : Measure (E d)) (v v' : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (fun w => grad (fun z => D₂ m w z) v') v

end MFGLimit.Conc


