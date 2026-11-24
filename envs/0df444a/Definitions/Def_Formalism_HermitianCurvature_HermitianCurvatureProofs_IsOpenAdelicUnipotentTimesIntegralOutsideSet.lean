-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:25:49.828916+00:00
-- url     : https://prove2.me/theorems/352bca1f-b6f7-4702-84d5-dbf223781262
-- title:
--   Is Open Adelic Unipotent Times Integral Outside Set
-- statement:
--   Definitions and structural lemmas for Is Open Adelic Unipotent Times Integral Outside Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenAdelicUnipotentTimesIntegralOutsideSet.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section gen
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
def hs (p v : Fin n → ℂ) (σ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - Matrix.vecMulVec p (fun j => herm H (bvec j) v) + Matrix.vecMulVec (v + σ • p) (fun j => herm H (bvec j) p)
end gen
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
def UP (k r : ℕ) (l : Fin r) : Set (Mx k r) :=
  {u | u ∈ Glev k r l.castSucc ∧ u *ᵥ bvec (eI k r l) = bvec (eI k r l) ∧
    ∀ y, herm (Hpk k r) y (bvec (eI k r l)) = 0 → ∃ t : ℂ, u *ᵥ y = y + t • bvec (eI k r l)}
def IsX (k r : ℕ) (l : Fin r) (x : Fin (2 * r + k + 1) → ℂ) : Prop :=
  herm (Hpk k r) x (bvec (eI k r l)) = 1 ∧ herm (Hpk k r) x x = 0 ∧
    ∀ a : Fin r, a.val < l.val → herm (Hpk k r) (bvec (eI k r a)) x = 0 ∧ herm (Hpk k r) (bvec (esI k r a)) x = 0
def hx (k r : ℕ) (l : Fin r) (x : Fin (2 * r + k + 1) → ℂ) : Mx k r :=
  hs (Hpk k r) (bvec (eI k r l))
    (x - bvec (esI k r l) - herm (Hpk k r) x (bvec (esI k r l)) • bvec (eI k r l)) (herm (Hpk k r) x (bvec (esI k r l)))
structure Dec (k r : ℕ) (l : Fin r) (g : Mx k r) (c : ℂ) (u g₁ u' : Mx k r) : Prop where
  hc : c ≠ 0
  hu : u ∈ UP k r l
  hg : g₁ ∈ Glev k r l.succ
  hu' : u' ∈ UP k r l
  eq : g = u * (w1 k r l c * g₁) * u'
def cF (k r : ℕ) (l : Fin r) (g : Mx k r) : ℂ := herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l))
def iH (g : Mx k r) : Mx k r := Hpk k r * gᴴ * Hpk k r
def uL (k r : ℕ) (l : Fin r) (g : Mx k r) : Mx k r := hx k r l ((cF k r l g)⁻¹ • (g *ᵥ bvec (eI k r l)))
def rho (k r : ℕ) (l : Fin r) (g : Mx k r) : Mx k r :=
  w1 k r l (conj (cF k r l g)) * iH (uL k r l g) * g * uL k r l (iH g)
section smooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}
def SmM (f : X → Matrix (Fin m) (Fin m) ℂ) (s : Set X) : Prop := ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s
def SmV (f : X → Fin m → ℂ) (s : Set X) : Prop := ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) s
end smooth
section smooth2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
end smooth2
def C0 (k r : ℕ) (l : Fin r) : Set (Mx k r) := {g | cF k r l g ≠ 0 ∧ cF k r l (iH g) ≠ 0}
section ext
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
def D0 (k r : ℕ) (l : Fin r) (D₁ : Set (Mx k r)) : Set (Mx k r) := C0 k r l ∩ rho k r l ⁻¹' D₁
def Jx (k r : ℕ) (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (φ : ℂ → ℂ) (Ψ : Mx k r → (Wq →L[ℂ] Wp)) (g : Mx k r) :
    Wq →L[ℂ] Wp :=
  (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) • (φ (cF k r l g) • Ψ (rho k r l g))
end ext
section transfer
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)
end transfer
end Formalism.FourierDecayAlt.P.Qx4
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


