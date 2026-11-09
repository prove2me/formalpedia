-- Prove2me | Definitions.Def_BosonicLearn_transcriptLaw
-- name    : BosonicLearn_transcriptLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:13.452192+00:00
-- url     : https://prove2.me/theorems/9456fcb4-f12c-497b-b205-d05f9a4107ad
-- title:
--   Transcript law $\mathcal T_\rho$ of an adaptive scheme
-- statement:
--   For an adaptive single-copy scheme $S$ on $N$ copies and a state $\rho$, $\mathcal T_\rho$ is the joint law on $\mathcal O^N$ of the $N$ outcomes when every round measures a fresh copy of $\rho$ with the POVM chosen from the earlier outcomes. In particular, for rank-one POVM elements $|\phi_t\rangle\langle\phi_t|$ the likelihood of a transcript is $\prod_t\langle\phi_t|\rho|\phi_t\rangle$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30; Eq. (63), p. 35

import Mathlib
import Definitions.Def_BosonicLearn_AdaptiveScheme
import Definitions.Def_BosonicLearn_sequentialLaw

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory

namespace BosonicLearn

/-- **Law `T_ρ` of the full transcript of an adaptive scheme.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "Let T_X(x) denote the likelihood of observing x when the underlying state is ρ_{R_X}",
with `x := x_{1:N}` the complete transcript; the copies are i.i.d. (`T_X(x) = ∏ₜ ⟨ϕ|ρ|ϕ⟩`, Eq. (63), p. 35).

`transcriptLaw S ρ` is the joint law on `O^N` of the `N` outcomes when every round measures a fresh copy of
the same state `ρ`. -/
noncomputable def transcriptLaw {n N : ℕ} {O : Type} [MeasurableSpace O] (S : AdaptiveScheme n N O)
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) : Measure (Fin N → O) :=
  sequentialLaw (S.round ρ) N le_rfl

end BosonicLearn


