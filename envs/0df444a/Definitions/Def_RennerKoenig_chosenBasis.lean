-- Prove2me | Definitions.Def_RennerKoenig_chosenBasis
-- name    : RennerKoenig_chosenBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:58.512008+00:00
-- url     : https://prove2.me/theorems/88860566-d98e-4676-b166-782916bea82e
-- title:
--   A fixed Hilbert basis of a Hilbert space
-- statement:
--   Every complex Hilbert space $K$ has a Hilbert basis. This definition fixes one, for use in computing traces.
--
--   **Formalization Note** The basis is selected by choice, with no separability assumption. Nothing in the mission depends on which basis is selected, because the trace of a trace-class operator does not.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.3 (the trace is used without naming a basis)

import Mathlib

namespace RennerKoenig

/-- **A fixed Hilbert basis of `K`**, used only to compute traces. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.3
uses `tr` without naming a basis.

**Formalization Note** Every Hilbert space has a Hilbert basis (`exists_hilbertBasis`); this is one
chosen by `Classical.choose`, with no separability assumption. Traces of trace-class operators do
not depend on it. -/
noncomputable def chosenBasis (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] :
    HilbertBasis (Classical.choose (exists_hilbertBasis ℂ K) : Set K) ℂ K :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ K))

end RennerKoenig


