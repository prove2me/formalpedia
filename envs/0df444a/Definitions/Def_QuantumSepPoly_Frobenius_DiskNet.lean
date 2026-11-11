-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_DiskNet
-- name    : QuantumSepPoly_Frobenius_DiskNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:00.919677+00:00
-- url     : https://prove2.me/theorems/0c7b9feb-1fc6-4188-9295-92cb4dc5da23
-- title:
--   Finite nets contained in the complex disk
-- statement:
--   For $\kappa\ge0$ and $\varepsilon>0$, an $\varepsilon$-net $E$ is contained in the closed disk $\{z:|z|\le\kappa\}$ and covers every point of that disk within $\varepsilon$.
--   $$N=\lceil4\kappa/\varepsilon\rceil+1.$$
--   Enumerate the square lattice with coordinates $(a-N)\varepsilon/2$, $0\le a\le2N$, and radially project exterior points onto the disk. Its finite image is the chosen net. The reduction uses the corresponding computed discretization parameters. Finite penalized optima are computed from assignments in $E^d$, not supplied separately. Net coverage and the universal cardinality bound are theorem targets.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 16 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Quartic

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- Finite nets of the closed complex disk; every net point remains inside the disk. -/
def IsDiskNet (E : Finset ℂ) (κ ε : ℝ) : Prop :=
  (∀ z ∈ E, ‖z‖ ≤ κ) ∧ ∀ z : ℂ, ‖z‖ ≤ κ → ∃ w ∈ E, ‖z - w‖ ≤ ε

/-- An explicit radial projection of a finite square grid. No optimizing choice is used. -/
def diskClip (κ : ℝ) (z : ℂ) : ℂ := if ‖z‖ ≤ κ then z else (κ / ‖z‖ : ℝ) • z

def diskGrid (κ ε : ℝ) : List ℂ :=
  let N := Nat.ceil (4 * κ / ε) + 1
  (List.range (2*N+1)).flatMap (fun a => (List.range (2*N+1)).map (fun b =>
    diskClip κ (((((a : ℝ) - N) * ε / 2 : ℝ) : ℂ) +
      Complex.I * (((b : ℝ) - N) * ε / 2))))

def diskNet (κ ε : ℝ) : Finset ℂ := by
  classical
  exact (diskGrid κ ε).toFinset

def alphabet (γ η : ℝ) : Finset ℂ := diskNet (discKappa γ η) (discEpsilon γ η)

def discreteValue {d : ℕ} (M : Bip d) (lam : ℝ) (E : Finset ℂ) : ℝ :=
  sSup {v | ∃ x y : Vec d, (∀ i, x i ∈ E) ∧ (∀ i, y i ∈ E) ∧ v = penalty M lam x y}

end QuantumSepPoly.Frobenius


