-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:20:29.043574+00:00
-- url     : https://prove2.me/theorems/84d26106-2f59-4342-8957-d1cd662b45c0
-- title:
--   Triangular Factor Middle Row
-- statement:
--   Definitions and structural lemmas for Triangular Factor Middle Row, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
section N1
variable {k r : ℕ}
variable (k r) in

def Ym (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => y a (esI k r (Fin.castLE hj b))
variable (k r) in

def Zv (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (b : Fin j) : Fin (2 * r + k + 1) → ℂ :=
  fun p => ∑ a, (Ym k r j hj y)⁻¹ b a * y a p
variable (k r) in

def Cf (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (l q : Fin (2 * r + k + 1)) : ℂ :=
  if h : r + k < q.val ∧ 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h.2⟩ l else 0
variable (k r) in

def Tn (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then
    (if r ≤ q.val ∧ q.val ≤ r + k then -(WeylGroupFacts.sgn k r q) * star (Cf k r j hj y q (tau k r p))
     else if r + k < q.val then
       (if h : 2 * r + k - q.val < j then Zv k r j hj y ⟨2 * r + k - q.val, h⟩ p
        else if h' : p.val < j then -star (Zv k r j hj y ⟨p.val, h'⟩ (tau k r q)) else 0)
     else 0)
  else if r ≤ p.val ∧ p.val ≤ r + k then Cf k r j hj y p q
  else 0
end N1
section MajorantSquareBound
variable {k r : ℕ}
end MajorantSquareBound
end
end Formalism.FourierDecayAlt.P.SignAntidiagonal


