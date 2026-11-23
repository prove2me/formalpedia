-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
-- name    : Formalism_UnipotentAdelicQuotients_EllReg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:03.198826+00:00
-- url     : https://prove2.me/theorems/af22f0f0-d7fc-49a2-b003-c4a6eec51973
-- title:
--   Ell Reg
-- statement:
--   Definitions and structural lemmas for Ell Reg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllReg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ZetaZeros.D.EllReg
open scoped ContDiff
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def ev {d : ℕ} (j : Fin d) : E d := EuclideanSpace.single j (1 : ℝ)
noncomputable def dw {d : ℕ} : List (Fin d) → (E d → ℂ) → E d → ℂ
  | [], f => f
  | j :: w, f => fun x => fderiv ℝ (dw w f) x (ev j)
noncomputable def trOp {d : ℕ} (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
    (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => b n w y * φ y) x
structure Sys (d : ℕ) (ι : Type) where
  ord : ι → ℕ
  a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ
noncomputable def Sys.tr {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (φ : E d → ℂ) (x : E d) : ℂ :=
  trOp (P.ord i) (P.a i) φ x
noncomputable def Sys.symb {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι) (x ξ : E d) : ℂ :=
  ∑ w : Fin (P.ord i) → Fin d, P.a i (P.ord i) w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)
def WeakSol {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  ∀ (i : ι) (φ : E d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, u x * P.tr i φ x = 0
def Hyp {d : ℕ} {ι : Type} (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ) : Prop :=
  IsOpen U ∧ (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) ∧
    (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) ∧ ContinuousOn u U ∧ WeakSol P U u
def Internal : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)) (u : E d → ℂ),
    Hyp P U u → ContDiffOn ℝ ∞ u U
end ZetaZeros.D.EllReg


