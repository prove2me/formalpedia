-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:59.062084+00:00
-- url     : https://prove2.me/theorems/90d5d5b3-76c0-4cc6-8a1c-e994ec5dc174
-- title:
--   NFRad Red S
-- statement:
--   Definitions and structural lemmas for NFRad Red S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
def LocSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ g₀ ∈ Glev k r (Fin.last r), 0 < GGl k r z z' g₀ →
      ∃ V : Set (Q.Mx k r), IsOpen V ∧ g₀ ∈ V ∧ ∃ a b : Q.Mx k r → Q.Mx k r,
        ContDiffOn ℝ ∞ a V ∧ ContDiffOn ℝ ∞ b V ∧
        ∀ g ∈ V, g ∈ Glev k r (Fin.last r) → 0 < GGl k r z z' g →
          a g ∈ UWset k r z ∧ b g ∈ UWset k r z' ∧
            g = a g * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * b g
def RepSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ h₀ ∈ UWset k r z, ∃ V : Set (Q.Mx k r), IsOpen V ∧ h₀ ∈ V ∧ ∃ P : Q.Mx k r → (Wp →L[ℂ] Wp),
      ContDiffOn ℝ ∞ P V ∧ ∀ h ∈ V, h ∈ UWset k r z → π h = P h
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (φ : (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp)) :
    Q.Fn k r (Wq →L[ℂ] Wp) := fun c g =>
  if h : (c, g) ∈ DomR k r z z' ∧ ∃ p : Q.Mx k r × Q.Mx k r, p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z' ∧
      g = p.1 * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * p.2 then
    (π (Classical.choose h.2).1).comp ((φ (c, zetaL k r z z' (Fin.last r) g)).comp (π' (Classical.choose h.2).2))
  else 0
end Formalism.FourierDecayAlt.P.NFRadRedS
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


