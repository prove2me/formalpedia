-- Prove2me | Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
-- name    : Formalism_IncomingBounds_FlowDegreeBounds_Cayley
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:06.494927+00:00
-- url     : https://prove2.me/theorems/19cc4e70-9e68-40fd-8672-82373499db96
-- title:
--   Cayley
-- statement:
--   Definitions and structural lemmas for Cayley, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds.Cay
open MvPolynomial Matrix
section Der
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)
end Der
end Formalism.IncomingBounds.Cay
namespace Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
section SupSum
variable {σ M : Type} [AddCommMonoid M] (f : (σ →₀ ℕ) → K → M)
end SupSum
def dm {σ : Type} (m : σ →₀ ℕ) (Q : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ a ∈ Q.support,
    if m ≤ a then monomial (a - m) (coeff a Q * ((mfact a : K) / (mfact (a - m) : K))) else 0
end Formalism.IncomingBounds.Cay
namespace Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
def Mg (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (PVar n) K) :=
  Matrix.of fun i j => X (Sum.inl (i, j))
end Formalism.IncomingBounds.Cay
namespace Formalism.IncomingBounds
open MvPolynomial Matrix
end Formalism.IncomingBounds


