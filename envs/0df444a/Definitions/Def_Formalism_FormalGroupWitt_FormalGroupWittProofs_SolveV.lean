-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:56.376467+00:00
-- url     : https://prove2.me/theorems/e59b6f49-e6e9-4712-a75d-f100f2d19618
-- title:
--   Solve V
-- statement:
--   Definitions and structural lemmas for Solve V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG.SolveVAux
open MvPowerSeries
section Low
variable {R : Type u} [CommRing R] {τ : Type w}
def Low (N : ℕ) (p : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < N → coeff d p = 0
end Low
section Prod
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
def P (k : ι → MvPowerSeries τ R) (e : ι →₀ ℕ) : MvPowerSeries τ R :=
  e.prod fun s n => k s ^ n
end Prod
section Subst
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
end Subst
section Main
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}
def phi (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (k : ι → MvPowerSeries τ R) :
    ι → MvPowerSeries τ R :=
  fun j => G j - subst k (g j)
def seq (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    ι → MvPowerSeries τ R :=
  (phi G g)^[n] 0
def lim (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) : ι → MvPowerSeries τ R :=
  fun i d => coeff d (seq G g (d.degree + 1) i)
variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}
end Main
end Formalism.FG.SolveVAux
namespace Formalism.FG
open MvPowerSeries SolveVAux
end Formalism.FG


