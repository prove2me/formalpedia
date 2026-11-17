-- Prove2me | Definitions.Def_SybilClinch_Supplement_zeroStartUtility
-- name    : SybilClinch_Supplement_zeroStartUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:16:31.447275+00:00
-- url     : https://prove2.me/theorems/3ad03ce2-711c-483e-b572-90d26ad76ea7
-- title:
--   Utility in the classical zero-start adaptive clinching auction
-- statement:
--   For a fixed supply $s$, a finite one-sided profile $P$, a group of identities $I$, and a true value $V$, the group's **classical zero-start utility** is the right limit
--
--   $$
--   u=\lim_{p_\star\downarrow0}\left(VX_I(p_\star)-Y_I(p_\star)\right),
--   $$
--
--   where $(X_I(p_\star),Y_I(p_\star))$ is the terminal group allocation and payment in a completed constant-target adaptive clinching run started at $p_\star>0$.
--
--   Appendix B proves that below the first-event threshold the positive-start outcome equals the classical zero-start auction outcome. The only exceptional profile has a single positive-value, positive-budget identity; there the positive-start allocation and payment converge to the whole supply at zero payment. Thus this definition covers the full classical zero-start auction.
--
--   **Formalization Note** The published `IsRun` relation includes the paper's simultaneous proportional allocation rule at tied stopping exits. Runs are required on a punctured right neighbourhood of zero, exactly as supplied by Lemma B.4.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Appendix B.1–B.3, printed pp.44–49 (PDF pp.46–51), especially Lemma B.4 and Corollary B.8

import Mathlib
import Definitions.Def_SybilClinch_Supplement_fixedMech
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_Run_alloc
import Definitions.Def_SybilClinch_Run_payOf

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Appendix B.1–B.3,
printed pp.44–49 (PDF pp.46–51): the true-value utility of a group `I` in the classical
zero-start adaptive clinching auction for supply `s`.

The zero-start utility is the right limit, as the positive start price tends to zero, of the
terminal utility in completed runs of the constant-target mechanism. Appendix B proves that this
is the classical zero-start auction outcome profile by profile: below the first-event threshold
the positive-start and zero-start outcomes coincide, except for the single-positive-identity
boundary case, where allocation and payment converge to the whole supply at zero payment.

**Formalization Note.** `IsRun` contains the paper's simultaneous proportional rule at tied
stopping exits. Requiring runs only on some punctured right neighbourhood of zero is exactly what
Lemma B.4 supplies. The family outside that neighbourhood is irrelevant to `𝓝[>] 0`. -/
noncomputable def zeroStartUtility (s : ℝ) (P : OneSidedProfile) (I : Finset ℕ)
    (V u : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ R : ℝ → Run,
    (∀ p ∈ Ioo 0 ε, IsRun (fixedMech s p) P (R p)) ∧
      Tendsto
        (fun p => V * (R p).alloc I (R p).pf - (R p).payOf (fixedMech s p) I (R p).pf)
        (𝓝[>] (0 : ℝ)) (𝓝 u)

end Supplement

end SybilClinch


