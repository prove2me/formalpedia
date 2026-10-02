-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel
-- name    : ProcessingNetworks_PacketNetworks_RPSFluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:02:11.854666+00:00
-- url     : https://prove2.me/theorems/da1cb6ce-46e8-4ee2-9fc0-d334348e618e
-- title:
--   The RPS fluid equation, the RPS fluid model and its stability (Eq. 12.65, Definition 12.25)
-- statement:
--   **The RPS fluid equation (12.65).** For each class $i$ belonging to link $k$,
--   $\hat Z_i(t) > 0 \implies \dot{\hat D}_i(t) = \frac{\hat Z_i(t)}{\hat Y_k(t)}\psi_k(\hat
--   Y(t))$, where $\hat Y(t) = A\hat Z(t)$ and $\psi(y)$ solves (12.57).
--
--   **Definition 12.25.** The RPS fluid model consists of equations (12.31)–(12.36) (mission
--   XII's `SatisfiesPacketFluidEquations`, which hold under any control policy) together with
--   (12.65). `RPSFluidStable` is stability of the RPS fluid model, the notion Theorems
--   12.27–12.28 use: there is $\delta>0$ with $\hat Z(t)=0$ for $t\ge\delta$ and every RPS fluid
--   model solution (the chapter's Definition 12.15 form; (12.32) fixes $|\hat Z(0)|=1$).
--
--   **Formalization note.** (12.65) is stated in existence form (`HasDerivAt`): where
--   $\hat Z_i(t)>0$, $\hat D_i$ is differentiable with the stated derivative, which is what the
--   proof of Theorem 12.24 establishes through (12.70) and what mission IX's (10.34) states, so
--   that Proposition 12.26's correspondence goes through. $\psi_k(\hat Y(t))$ is evaluated with
--   mission IX's `psi`, legitimate here because the coordinate $k$ of a solution of (12.57) is the
--   same for every solution when $y_k>0$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 251 (PDF p. 267), Definition 12.25, Eq. (12.65)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSRawModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- The RPS fluid equation (12.65), Dai & Harrison p. 251 (PDF p. 267): for each class `i`
belonging to link `k`, whenever `Ẑᵢ(t) > 0` the class-level departure rate is
`(d/dt) D̂ᵢ(t) = (Ẑᵢ(t)/Ŷₖ(t)) ψₖ(Ŷ(t))`, where `Ŷ(t) = A Ẑ(t)` and `ψ(y)` solves the RPS
optimization problem (12.57) (mission IX's `psi` over `⟨C⟩`; the coordinate `ψₖ(y)` is the
same for every solution when `yₖ > 0`). -/
def SatisfiesRPSFluidEquation {I K : ℕ} (fr : FixedRoutingData I K) (Dh Zh : ℝ → Fin I → ℝ) :
    Prop :=
  ∀ t : ℝ, 0 < t → ∀ i : Fin I, 0 < Zh t i →
    HasDerivAt (fun u => Dh u i)
      (Zh t i / ProportionalFairness.groupAggregate fr.linkDesig (Zh t) (fr.linkDesig i) *
        ProportionalFairness.psi (hullFinset fr.cfg.C)
          (ProportionalFairness.groupAggregate fr.linkDesig (Zh t)) (fr.linkDesig i)) t

/-- Definition 12.25, Dai & Harrison p. 251 (PDF p. 267): the RPS fluid model consists of the
general fluid equations (12.31)-(12.36) and the RPS fluid equation (12.65). -/
def IsRPSFluidModelSolution {I K : ℕ} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (lam : Fin I → ℝ) (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ) :
    Prop :=
  SatisfiesPacketFluidEquations fr.dat S lam Dh Th Zh ∧ SatisfiesRPSFluidEquation fr Dh Zh

/-- Stability of the RPS fluid model (Theorems 12.27–12.28, "the RPS fluid model is stable"; the
chapter's notion, Definition 12.15's form, since (12.32) fixes `|Ẑ(0)| = 1`): there is a `δ > 0`
such that every RPS fluid model solution has `Ẑ(t) = 0` for all `t ≥ δ`. -/
def RPSFluidStable {I K : ℕ} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (lam : Fin I → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
    IsRPSFluidModelSolution fr S lam Dh Th Zh → ∀ t : ℝ, δ ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.PacketNetworks


