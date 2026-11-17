-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_auxTnear
-- name    : GraphNNSphere_Supplement_auxTnear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:49:04.030125+00:00
-- url     : https://prove2.me/theorems/eedd788b-b280-4bab-8d0f-7a7ed3f4088f
-- title:
--   Auxiliary exposure procedure, $T_{\mathrm{near}}$, $\theta_{\mathrm{trap}}$, $\rho_+$ and the event $C$
-- statement:
--   For a neighbor radius $\rho$ the **trap distance** $\theta_{\mathrm{trap}}$ solves $\sin^2\theta_{\mathrm{trap}}=(1-\cos\rho)^2/(2(1-\cos\rho)-\sin^2\theta_1)$, the **exposure radius** $\rho_+$ solves $nF(\rho_+)=2\Delta$, and $C$ is the data event that every cap $C(x,\rho_+)$ around a data point contains at least $\Delta$ other data points (for $G_\rho$, $C$ is the whole space).
--
--   The **auxiliary exposure procedure** runs alongside a local exploration algorithm: an entry request reveals that point, and an expansion of $x$ reveals every data point in $C(x,\rho_+)$. It stops at the end of its first operation revealing a point of the target cap $C(q,b_0)$, at an expansion whose cap holds fewer than $\Delta$ other points (for $N_\Delta$: the list cannot be reconstructed), or when the algorithm terminates; a triggering operation is completed. **$T_{\mathrm{near}}$** is the number of expansions at query distances in $(b_0,\theta_{\mathrm{trap}}+\rho_+]$ through this stop.
--
--   **Formalization Note** Until its stop the procedure's lists are the true lists (for $N_\Delta$, the $\Delta$ nearest other points of a cap holding at least $\Delta$ others are the true list), so $T_{\mathrm{near}}$ is computed from the algorithm's actual history.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, pp.59, 63–64; Theorem 5.5

import Mathlib
import Definitions.Def_GraphNNSphere_theta1
import Definitions.Def_GraphNNSphere_capRadius
import Definitions.Def_GraphNNSphere_Supplement_LocalExplorer

namespace GraphNNSphere

namespace Supplement

/-- The trap distance `θ_trap` for the neighbor radius `ρ`:
`sin² θ_trap = (1 - cos ρ)²/(2(1 - cos ρ) - S)`, `S = sin² θ₁`, with `θ_trap ∈ (θ₁, π/2)`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.59). -/
noncomputable def thetaTrap (n d : ℕ) (ρ : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt ((1 - Real.cos ρ) ^ 2 / (2 * (1 - Real.cos ρ) - Real.sin (theta1 n d) ^ 2)))

/-- The exposure radius `ρ₊`, defined by `nF(ρ₊) = 2Δ` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.63). -/
noncomputable def rhoPlus (n d Δ : ℕ) : ℝ := capRadius d (2 * (Δ : ℝ) / (n : ℝ))

/-- The data event `C` for `N_Δ`: every cap `C(x, ρ₊)` around a data point contains at least `Δ` other
data points (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.63). For `G_ρ` the event is the whole sample space. -/
def CEventNN {n d : ℕ} (ρp : ℝ) (Δ : ℕ) : Set (Fin n → Sph d) :=
  {X | ∀ x : Fin n, Δ ≤ (Finset.univ.filter (fun j => j ≠ x ∧ geo (X x) (X j) ≤ ρp)).card}

/-- The state of the auxiliary exposure procedure: revealed labels, whether it has stopped, and the
count `T_near` so far. -/
structure AuxState (n : ℕ) where
  revealed : Finset (Fin n)
  stopped : Bool
  tnear : ℕ

open Classical in
/-- One operation of the auxiliary exposure procedure of Theorem 5.5 (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, pp.63–64), run
alongside the algorithm. An entry request reveals that point; an expansion of `v` reveals every
data point of `C(X_v, ρ₊)`, and it is counted in `T_near` when `δ(q, X_v) ∈ (b₀, b₁]`,
`b₁ = θ_trap + ρ₊`. The procedure stops at the end of its first operation revealing a point of
`C(q, b₀)`, and, for `N_Δ` (`nn = true`), at an expansion whose cap holds fewer than `Δ` other points
(the exceptional stop: the list cannot be reconstructed). Each operation that triggers a stop is
completed.

**Formalization Note** Until its stop the procedure's lists are the true lists (for `N_Δ` the `Δ`
nearest other points of a cap with at least `Δ` others are the true list), so it is driven by the
algorithm's actual history. -/
noncomputable def auxObs {n d : ℕ} (X : Fin n → Sph d) (q : Sph d) (ρp b₀ b₁ : ℝ) (nn : Bool)
    (Δ : ℕ) (s : AuxState n) : ExplObs n d → AuxState n
  | .entry i _ =>
    if s.stopped then s else
      ⟨insert i s.revealed, decide (∃ j ∈ insert i s.revealed, geo q (X j) ≤ b₀), s.tnear⟩
  | .expand v _ =>
    if s.stopped then s else
      ⟨s.revealed ∪ Finset.univ.filter (fun j => geo (X v) (X j) ≤ ρp),
        decide ((∃ j ∈ s.revealed ∪ Finset.univ.filter (fun j => geo (X v) (X j) ≤ ρp),
              geo q (X j) ≤ b₀) ∨
            (nn = true ∧ (Finset.univ.filter (fun j => j ≠ v ∧ geo (X v) (X j) ≤ ρp)).card < Δ)),
        s.tnear + (if b₀ < geo q (X v) ∧ geo q (X v) ≤ b₁ then 1 else 0)⟩

/-- `T_near`: the number of expansions at query distances in `(b₀, b₁]` through the stop of the
auxiliary exposure procedure, for the algorithm with budget `(T, E)` on the graph `G`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.5, pp.63–64). -/
noncomputable def auxTnear {n d : ℕ} {Ω : Type} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) (A : LocalExplorer n d Ω) (ω : Ω) (T E : ℕ∞) (ρp b₀ b₁ : ℝ) (nn : Bool) (Δ : ℕ) : ℕ∞ :=
  ⨆ t, (((explRun G X q k A ω T E t).hist.foldl (auxObs X q ρp b₀ b₁ nn Δ) ⟨∅, false, 0⟩).tnear : ℕ∞)

end Supplement

end GraphNNSphere


