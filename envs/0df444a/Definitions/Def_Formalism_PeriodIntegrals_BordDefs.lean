-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BordDefs
-- name    : Formalism_PeriodIntegrals_BordDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:31.600809+00:00
-- url     : https://prove2.me/theorems/09aef0ab-9782-42e9-840b-3cd82965e3ea
-- title:
--   Bord Defs
-- statement:
--   Definitions and structural lemmas for Bord Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BordDefs.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI
open Formalism.QuantumDeterminants
def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)
def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb
def omF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ • prW k (wbPart k r z) (Matrix.mulVec μ (wbPart k r z'))
def omF' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) • prW k (wbPart k r z') (Matrix.mulVec μ⁻¹ (wbPart k r z))
def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))
def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))
def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)
end PI


