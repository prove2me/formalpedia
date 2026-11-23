-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:47.736501+00:00
-- url     : https://prove2.me/theorems/f3177285-85eb-49e2-864d-40f2b29a00e3
-- title:
--   Transvection Inv
-- statement:
--   Definitions and structural lemmas for Transvection Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/TransvectionInv.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
abbrev FinalTheorems (m n : ℕ) := (Fin n × Fin m) ⊕ (Fin n × Fin m)
def phi (ε : Fin m → Bool) : FinalTheorems m n → (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)
  | Sum.inl x => if ε x.2 then Sum.inl (x.2, x.1, false) else Sum.inr (x.2, x.1, true)
  | Sum.inr y => if ε y.2 then Sum.inr (y.2, y.1, false) else Sum.inl (y.2, y.1, true)
def Dsrc (i j : Fin n) : Derivation ℂ (MvPolynomial (FinalTheorems m n) ℂ) (MvPolynomial (FinalTheorems m n) ℂ) :=
  mkDerivation ℂ (Sum.elim (fun x : Fin n × Fin m => if x.1 = j then X (Sum.inl (i, x.2)) else 0)
    (fun y : Fin n × Fin m => if y.1 = i then -X (Sum.inr (j, y.2)) else 0))
def act (g : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ :=
  aeval (Sum.elim (fun x : Fin n × Fin m => ∑ k, C (g x.1 k) * X (Sum.inl (k, x.2)))
    (fun y : Fin n × Fin m => ∑ k, C (g⁻¹ k y.1) * X (Sum.inr (k, y.2))))
def wgt (l : Fin n) (d : FinalTheorems m n →₀ ℕ) : ℤ :=
  ∑ a : Fin m, (d (Sum.inl (l, a)) : ℤ) - ∑ b : Fin m, (d (Sum.inr (l, b)) : ℤ)
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
namespace PositivityTheory.Rg.Sw.LC
end PositivityTheory.Rg.Sw.LC


