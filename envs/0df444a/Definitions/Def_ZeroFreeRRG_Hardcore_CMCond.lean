-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_CMCond
-- name    : ZeroFreeRRG_Hardcore_CMCond
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:36:56.711136+00:00
-- url     : https://prove2.me/theorems/3c2a98c8-f733-409c-a327-dd1c479e2871
-- title:
--   Conditional probability for a uniform configuration-model pairing
-- statement:
--   For events $C$ and $P$ on the finite set of configuration-model pairings on $n$ vertices of degree $d$, this defines the conditional probability
--   $$
--   \Pr_{\mathrm{CM}_{n,d}}[P\mid C]
--   =\frac{\#\{M:C(M)\text{ and }P(M)\}}{\#\{M:C(M)\}}.
--   $$
--   The uniform pairing is the configuration model $\mathrm{CM}_{n,d}$. Conditional probabilities are used in the proof of Theorem 5.1 with $C=\{X_{1,n}=X_{2,n}=0\}$, the event that the multigraph has no self-loops or parallel edges.
--
--   **Formalization Note.** As for the already published finite-average `cmProb`, a zero denominator gives Lean's quotient $0$. The asymptotic statements restrict to admissible $n$ (with $nd$ even), and the simplicity event is eventually nonempty in the intended range.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Theorem 5.1, p. 40 (PDF p. 41), conditioning on X_{1,n}=X_{2,n}=0; finite configuration model from Definition 2.2, p. 16.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph

open scoped Classical

namespace ZeroFreeRRG.Hardcore

open AFIsingKS

/-- The probability of `P` conditional on `C` for the uniform configuration-model pairing.
As with `cmProb`, the denominator is zero for an empty conditioning event (and in particular
when the pairing type is empty); the limiting statements in which this is used quantify over
admissible sizes. -/
noncomputable def cmCondProb {n d : ℕ} (C P : Matching n d → Prop) : ℝ :=
  ((Finset.univ.filter (fun M => C M ∧ P M)).card : ℝ) /
    ((Finset.univ.filter C).card : ℝ)

end ZeroFreeRRG.Hardcore


