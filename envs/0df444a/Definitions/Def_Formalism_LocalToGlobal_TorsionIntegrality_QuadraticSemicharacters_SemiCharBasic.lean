-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:17.618287+00:00
-- url     : https://prove2.me/theorems/51c827f9-4895-4bc1-a60c-ad51b2aaeb5e
-- title:
--   Semi Char Basic
-- statement:
--   Definitions and structural lemmas for Semi Char Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/SemiCharBasic.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
def OpUMul : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (x y : V) (F : V → ℂ) (z : V),
    opU H x (opU H y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) * opU H (x + y) F z
def OpUComm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (F : V → ℂ) (z : V),
    opU H 0 F z = F z ∧ ∀ x y : V,
    opU H x (opU H y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * opU H y (opU H x F) z
def OpUNorm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (x : V) (F : V → ℂ) (z : V),
    ‖opU H x F z‖ ^ 2 * Real.exp (-Real.pi * (H z z).re)
      = ‖F (z + x)‖ ^ 2 * Real.exp (-Real.pi * (H (z + x) (z + x)).re)
def OpUIsom : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W)
    (g : V →ₗ[ℂ] W), IsIsom H H' g → ∀ (x : V) (G : W → ℂ) (z : V),
    opU H x (fun v => G (g v)) z = opU H' (g x) G (g z)
def PullOpU : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (δ : V ≃ₗ[ℂ] V), IsIsom H H (δ : V →ₗ[ℂ] V) →
    ∀ (x : V) (F : V → ℂ) (z : V), pullInv δ (opU H x F) z = opU H (δ x) (pullInv δ F) z
def SemiCharBasic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → α 0 = 1 ∧ (∀ x ∈ Λ, α (-x) = α x) ∧ Λ ≤ dualLat H Λ
def SemiHom : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V), IsHerm H → ∀ (Λ : AddSubgroup V) (α : V → ℂ),
    IsSemiChar H Λ α → ∀ x ∈ Λ, ∀ y ∈ Λ, ∀ (F : V → ℂ) (z : V),
      α x * opU H x (fun v => α y * opU H y F v) z = α (x + y) * opU H (x + y) F z
def OpUAnalytic : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V) (x : V)
    (F : V → ℂ), AnalyticOnNhd ℂ F Set.univ → AnalyticOnNhd ℂ (opU H x F) Set.univ
def MatHBasic : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : n → ℂ, matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j)) ∧ (h.IsHermitian → IsHerm (matH h))
def StdHBasic : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n],
    (∀ z w : n → ℂ, stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i)) ∧ IsHerm (stdH L n) ∧
      IsPosDef (stdH L n)
def OpUStd : Prop :=
  ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (x : n → ℂ) (f : n → ℂ → ℂ) (z : n → ℂ),
    opU (stdH L n) x (prodFn f) z = ∏ i, Formalism.L2.Th1.F.opU L (x i) (f i) (z i)
def OpUBlk4 : Prop :=
  ∀ (n : Type) [Fintype n] (h : Matrix n n ℂ),
    (∀ z w : Fin 4 × n → ℂ, matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w)) ∧
    ∀ (x : Fin 4 × n → ℂ) (θ : Fin 4 → (n → ℂ) → ℂ) (z : Fin 4 × n → ℂ),
      opU (matH (blk4 h)) x (fun v => ∏ a, θ a (slice a v)) z = ∏ a, opU (matH h) (slice a x) (θ a) (slice a z)
end Formalism.L2.Th1.H


