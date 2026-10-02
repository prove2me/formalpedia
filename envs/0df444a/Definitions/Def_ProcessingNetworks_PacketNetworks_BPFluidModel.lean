-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_BPFluidModel
-- name    : ProcessingNetworks_PacketNetworks_BPFluidModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:55:13.744762+00:00
-- url     : https://prove2.me/theorems/e9fab1af-ccbd-4910-94e7-4621dc984982
-- title:
--   Regular points and the back-pressure fluid equation (Eq. 12.44)
-- statement:
--   On top of mission XII's `ProcessesAndFluidModel` (imported): `RegularPoint` (a point $t\ge 0$
--   where the fluid limit path $(\hat D,\hat T,\hat Z)$ is differentiable, the notion introduced
--   just before Lemma 12.20) and the **back-pressure fluid equation (12.44)**,
--   $$\hat Z(t)\cdot R\,\dot{\hat D}(t) = \max_{s\in\langle S\rangle} \hat Z(t)\cdot Rs$$ at each
--   regular point $t\ge 0$ (`SatisfiesBackPressureFluidEquation`), and
--   `IsBackPressureFluidModelSolution` (Eqs. 12.31–12.36 together with 12.44).
--
--   **Formalization note.** (12.44) is imposed at regular points of the path, i.e. where
--   $\hat D$, $\hat Z$ and every $\hat T_s$ are differentiable, as the book defines them; imposing
--   it wherever $\hat D$ alone is differentiable would be a stronger equation than Lemma 12.20
--   establishes. Differentiability is within the time domain $[0,\infty)$ (one-sided at $t=0$),
--   since the paths are only determined there. The maximum over $\langle S\rangle$ is phrased via
--   domination by an explicit witness `shat`, not `sSup`/`⨆`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 241-242, Lemma 12.20, Eq. (12.44) (fluid apparatus restated from mission XII)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- A point `t ≥ 0` is regular for a fluid limit path `(D̂,T̂,Ẑ)` (the sentence just before
Lemma 12.20, p. 241, PDF p. 257) if the path is differentiable at `t`: `D̂`, `Ẑ` and each `T̂ₛ`
(`s ∈ S`) differentiable at `t`, within the time domain `[0,∞)` (one-sided at `t = 0`, two-sided
elsewhere). -/
def RegularPoint {J : ℕ} (S : Finset (Fin J → ℕ)) {I : ℕ} (Dh : ℝ → Fin J → ℝ)
    (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ) (t : ℝ) : Prop :=
  DifferentiableWithinAt ℝ Dh (Set.Ici 0) t ∧
    (∀ s ∈ S, DifferentiableWithinAt ℝ (fun u => Th u s) (Set.Ici 0) t) ∧
    DifferentiableWithinAt ℝ Zh (Set.Ici 0) t

/-- The back-pressure fluid equation (12.44), Dai & Harrison p. 242 (PDF p. 258): at each regular
point `t ≥ 0`, `Ẑ(t)·R(d/dt)D̂(t) = max_{s∈⟨S⟩} Ẑ(t)·Rs`, phrased via the derivative vector `d` of
`D̂` at `t` (within `[0,∞)`) and via domination over `⟨S⟩` for the maximum. -/
def SatisfiesBackPressureFluidEquation {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
    (Zh : ℝ → Fin I → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → RegularPoint S Dh Th Zh t → ∀ d : Fin J → ℝ,
    HasDerivWithinAt Dh d (Set.Ici 0) t →
    ∃ shat ∈ hullFinset S,
      (∀ s' ∈ hullFinset S, Zh t ⬝ᵥ (R dat).mulVec s' ≤ Zh t ⬝ᵥ (R dat).mulVec shat) ∧
      Zh t ⬝ᵥ (R dat).mulVec d = Zh t ⬝ᵥ (R dat).mulVec shat

/-- A fluid model solution under the back-pressure control policy (Section 12.3, "Fluid
models", and Lemma 12.21): (12.31)-(12.36) plus the back-pressure fluid equation (12.44). -/
def IsBackPressureFluidModelSolution {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
    (Zh : ℝ → Fin I → ℝ) : Prop :=
  SatisfiesPacketFluidEquations dat S lam Dh Th Zh ∧
    SatisfiesBackPressureFluidEquation dat S Dh Th Zh

end ProcessingNetworks.PacketNetworks


