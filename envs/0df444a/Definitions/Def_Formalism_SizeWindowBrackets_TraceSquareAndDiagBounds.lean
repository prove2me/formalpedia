-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
-- name    : Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:36.994796+00:00
-- url     : https://prove2.me/theorems/4559a6bd-9b8b-4e22-854b-172f6bc9def1
-- title:
--   Trace Square And Diag Bounds
-- statement:
--   Definitions and structural lemmas for Trace Square And Diag Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/TraceSquareAndDiagBounds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
def hsSq {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2
def hsNorm {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (hsSq M)
section Family
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
def Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u u' : ι) :
    Matrix (Fin (d u)) (Fin (d u')) ℂ :=
  ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) • ((B u)ᴴ * B u')
def Kd (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u : ι) :
    Matrix (Fin (d u)) (Fin (d u)) ℂ :=
  Kp B ga u u
def Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ u, ((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)
def Rs (d : ι → ℕ) : ℝ := ∑ u, (d u : ℝ)
def F1 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (η : ℝ) : Prop :=
  (Qm B ga * Qm B ga).trace.re ≤ (1 + η) * (Qm B ga).trace.re ^ 2 / (D : ℝ)
def F2 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (e : ℝ) : Prop :=
  ∑ u, hsSq (Kd B ga u - 1) ≤ e * Rs d
def InputS (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar) ∧
  (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) ∧
  (D : ℝ) ≤ (1 + η1) * Dstar
def Isom {r : ι → ℕ} (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : Prop :=
  ∀ u, (V u)ᴴ * V u = 1
def Bram {r : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ :=
  fun u => B u * V u
end Family
def TraceIdentities : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ), (∀ u, 0 ≤ ga u) →
    (Qm B ga).trace = ∑ u, (Kd B ga u).trace ∧
    (Qm B ga).trace = (((∑ u, (Kd B ga u).trace.re : ℝ)) : ℂ) ∧
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ)
def TraceLower : Prop :=
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ),
    (n : ℝ) - Real.sqrt n * hsNorm (K - 1) ≤ K.trace.re
def CorBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar η0 η1 e0 : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → -1 ≤ η0 → 0 ≤ e0 → InputS B ga Dstar η0 η1 e0 →
    (Qm B ga * Qm B ga).trace.re
        ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d ∧
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re
def TraceSquareAndDiagBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputS B ga Dstar η0 η1 e0 →
    F1 B ga (5 * sg) ∧ F2 B ga e0 ∧ e0 ≤ 1 / 4
def RamCompress : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ),
    Isom V → ∀ u,
    Kd (Bram B V) ga u = (V u)ᴴ * Kd B ga u * V u ∧
    hsNorm (Kd (Bram B V) ga u - 1) ≤ hsNorm (Kd B ga u - 1)
def RamLoewner : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ),
    Isom V → (∀ u, 0 ≤ ga u) →
    (Qm (Bram B V) ga).PosSemidef ∧ (Qm B ga - Qm (Bram B V) ga).PosSemidef
def RamTrace : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 ≤ de → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (Qm B ga).trace.re - (de + Real.sqrt (de * e0)) * Rs d ≤ (Qm (Bram B V) ga).trace.re
def CompressDiagDefectBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → de ≤ 1 / 2 → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (1 - de) * Rs d ≤ Rs r ∧ F2 (Bram B V) ga (2 * e0)
def CompressTraceSquareBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (Dstar sg η0 η1 e0 de : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 → ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    InputS B ga Dstar η0 η1 e0 →
    F1 (Bram B V) ga (5 * sg + 3 * Real.sqrt de)
end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare


