-- Prove2me | Definitions.Def_RepairSched_Model_IsFeasible
-- name    : RepairSched_Model_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:16.70522+00:00
-- url     : https://prove2.me/theorems/1e4d0f90-adae-4fdf-8e92-56f660054ad0
-- title:
--   Feasibility for the EWF (10)
-- statement:
--   A tuple $(W,I,E,a,S)$ is feasible for the EWF if
--   $$W(t)=X(t)+\theta t-\sum_i\frac{\lambda_i}{\mu_i}\int_0^t(a_i(s)-S_i)^+\,ds+I(t)-E(t),\quad t\ge0,$$
--   $I(0)=E(0)=0$, the processes $I,E$ are càdlàg, nondecreasing and adapted, $a(t)\in\mathcal A(W(t))$, $S_i\ge0$, $W(t)\ge0$, and $a$ is adapted.
--
--   Work conservation is not imposed (p.16), and $E$ may jump.
--
--   **Formalization Note** Every clause holds for all $\omega$ and $t\ge0$. The allocation $a(t,W(t,\omega),\omega)$ is used only along the path, so it is one process $a_t(\omega)$. Constraint (10f) is read as progressive measurability together with integrability of the paths $s\mapsto(a_i(s)-S_i)^+$ on every $[0,t]$: the paper integrates these paths and applies Tonelli's theorem in (A.47).
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (10b)–(10f), p.17

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_allocSet
import Definitions.Def_RepairSched_IsCadlag

open MeasureTheory Set

namespace RepairSched

/-- **Feasibility for the EWF (10)**: `(W, I, E, a, S)` satisfies (10b)–(10f).
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), p.17: `W(t) = X(t) + θt − Σᵢ (λᵢ/μᵢ) ∫₀ᵗ (aᵢ(s,W(s)) − Sᵢ)⁺ ds + I(t) − E(t)` (10b);
`I(0) = E(0) = 0`, and `I`, `E` are in `D`, nondecreasing and `𝔽`-adapted (10c);
`a(t, W(t,ω), ω) ∈ A(W(t,ω))` (10d); `Sᵢ, W(t) ≥ 0` (10e); `a(·, W(·))` is `𝔽`-adapted (10f).

**Formalization Note.** Every clause is required for all `ω` and `t ≥ 0`. The allocation is used
only along the path, so it is the single process `a t ω`. (10f) is read as progressive
measurability, with `a` set to `0` at negative times, together with integrability of the paths
`s ↦ (aᵢ(s) − Sᵢ)⁺` on every `[0,t]`: the paper integrates these paths in (10a)–(10b) and applies
Tonelli's theorem in (A.47). Work conservation is not imposed (p.16). -/
def Model.IsFeasible {n : ℕ} (M : Model n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝔽 : Filtration ℝ mΩ) (X : ℝ → Ω → ℝ) (S : Fin n → ℝ) (W I E : ℝ → Ω → ℝ)
    (a : ℝ → Ω → Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ S i) ∧
    IsStronglyProgressive 𝔽 (fun t ω => if 0 ≤ t then a t ω else 0) ∧
    (∀ ω i t, 0 ≤ t → IntervalIntegrable (fun s => max (a s ω i - S i) 0) volume 0 t) ∧
    (∀ t, 0 ≤ t → StronglyMeasurable[𝔽 t] (I t) ∧ StronglyMeasurable[𝔽 t] (E t)) ∧
    (∀ ω, I 0 ω = 0 ∧ E 0 ω = 0 ∧
      MonotoneOn (fun t => I t ω) (Ici 0) ∧ MonotoneOn (fun t => E t ω) (Ici 0) ∧
      IsCadlag (fun t => I t ω) ∧ IsCadlag (fun t => E t ω)) ∧
    (∀ t ω, 0 ≤ t → 0 ≤ W t ω ∧ a t ω ∈ M.allocSet (W t ω)) ∧
    ∀ t ω, 0 ≤ t → W t ω = X t ω + M.theta * t -
      (∑ i, M.lam i / M.mu i * ∫ s in (0 : ℝ)..t, max (a s ω i - S i) 0) + I t ω - E t ω

end RepairSched


