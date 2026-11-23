-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:57.163906+00:00
-- url     : https://prove2.me/theorems/18be0105-0c3d-4358-a2f8-e308fd740c9a
-- title:
--   Symmetric Filtration Iff Supported
-- statement:
--   Definitions and structural lemmas for Symmetric Filtration Iff Supported, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymmetricFiltrationIffSupported.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
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
namespace PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
def S1 (ε : Fin m → Bool) : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) := {v | inF1 ε (Sum.elim id id v)}
def ed (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℕ := ∑ k, t (Sum.inr k)
def EtaEq (r : Sym m n) (d : ℕ) : Prop := ∀ t ∈ r.support, ed t = d
def EtaGt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, N < ed t
def pdeg (ε : Fin m → Bool) (a b : Fin m) : ℕ := (if ε a then 0 else 1) + (if ε b then 1 else 0)
def PA (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => opL (pairSym (n := n) ε ab.1 ab.2))
end PositivityTheory.Rg.Sw.LC.B3


