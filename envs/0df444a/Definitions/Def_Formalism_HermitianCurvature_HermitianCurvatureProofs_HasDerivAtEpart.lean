-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T18:52:49.94216+00:00
-- url     : https://prove2.me/theorems/ac8dd592-4314-4b56-9dec-7116ed7627dd
-- title:
--   Has Deriv At Epart
-- statement:
--   Definitions and structural lemmas for Has Deriv At Epart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtEpart.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
abbrev FS (k r nf : ℕ) : Type := List (CT k r nf × List (Mat k r))
def shape (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (L : FS k r nf) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (L.map fun e => cv D fib e.1 g (Rw e.2 F g)).sum
def stepOne (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) : FS k r nf :=
  (dco D X e.1).map (fun t' => (t', e.2)) ++ [(e.1, X :: e.2)]
def step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (L : FS k r nf) : FS k r nf := L.flatMap (stepOne D X)
def steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L : FS k r nf) : FS k r nf := w.foldr (step D) L
def Good {nf : ℕ} (L : Finset (Fin (r + 2))) (e : CT k r nf × List (Mat k r)) : Prop :=
  (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → l ∈ L ∨ l = Fin.last (r + 1)) ∧
  (∀ x ∈ e.1.es, ∀ Y ∈ x.2, inLie k r Y) ∧ (∀ Y ∈ e.2, inLie k r Y)
end Formalism.FourierDecayAlt.P.MinorPolynomials


