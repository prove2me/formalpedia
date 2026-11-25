-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:22:14.65301+00:00
-- url     : https://prove2.me/theorems/28394b4e-a83f-54fa-a542-554190e220a6
-- title:
--   NFRad Red Loc Sec
-- statement:
--   Definitions and structural lemmas for NFRad Red Loc Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedLocSec.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
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
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Trans
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
def tth (a b : Fin m → ℂ) : ℂ := -(herm H a b / ((‖herm H a b‖ : ℝ) : ℂ))
def tmat (a b : Fin m → ℂ) (q : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  TwoByOneBlock.qrefl H b ((star (tth H a b) - 1) / (q : ℂ)) *
    TwoByOneBlock.qrefl H (a + (-(tth H a b)) • b) (-1 / ((q : ℂ) - ((-‖herm H a b‖ : ℝ) : ℂ)))
variable {H}
end Trans
section Smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}
end Smooth
section Main
variable {k r : ℕ}
def u1 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z' + (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z
def u2 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a₀ : Q.Mx k r) (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  (a₀⁻¹ * g) *ᵥ z' + (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z
def qf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) : ℝ :=
  (Complex.normSq (zetaL k r z z' (Fin.last r) g) - Tz k r z * Tz k r z') / Tz k r z
def af (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (a₀ : Q.Mx k r) (g : Q.Mx k r) : Q.Mx k r :=
  a₀ * tmat (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g) (qf k r z z' g)
def bf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (a₀ : Q.Mx k r) (g : Q.Mx k r) : Q.Mx k r :=
  Hpk k r * (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g))ᴴ * Hpk k r * g
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
end Main
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


