-- Prove2me | Definitions.Def_AvgPHETH_SigmaPO
-- name    : AvgPHETH_SigmaPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:55.524027+00:00
-- url     : https://prove2.me/theorems/8ee6a64f-c433-437e-8faa-8b28329cb5da
-- title:
--   The class $\Sigma_d^{p,O}$
-- statement:
--   A language $L$ is in $\Sigma_d^{p,O}$ if there are a polynomial $p$ and a verifier $V$, polynomial-time with oracle $O$, such that
--
--   $$x\in L\iff \exists y_1\,\forall y_2\cdots Q_d y_d\; V(x,y_1,\dots,y_d),\qquad |y_i|=p(|x|).$$
--
--   Thus $\Sigma_0^{p,O}=\mathrm{P}^O$. Unrelativized classes are the case of the empty oracle: $\mathrm{NP}=\Sigma_1^{p,\emptyset}$ and $\Sigma_2^p=\Sigma_2^{p,\emptyset}$, since a machine with oracle $\emptyset$ gets the answer "no" to every query.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); Theorem 4.7, p.18 (PDF 20)

import Mathlib
import Definitions.Def_KarpLiptonOM_Alt
import Definitions.Def_AvgPHETH_PolyPredO
open KarpLiptonOM

namespace AvgPHETH

/-- The class `Σ_d^{p,O}`: languages `L` with `x ∈ L ⟺ ∃y₁ ∀y₂ ⋯ Q_d y_d V(x, y₁, …, y_d)`, for a
verifier `V` polynomial-time with oracle `O` and moves of a common polynomial length
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4); relativized as in Theorem 4.7, p.18 (PDF 20) and Remark 6.4, p.28 (PDF 30)).

**Formalization Note** `SigmaPO O 0 = P^O`, `NP = SigmaPO ∅ 1`, `Σ₂^p = SigmaPO ∅ 2`. The oracle `∅`
answers every query "no", so a machine with oracle `∅` is an unrelativized machine. -/
def SigmaPO (O : Set (List Bool)) (d : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (V : List (List Bool) → Prop), PolyPredO O (d + 1) V ∧
    ∀ x : List Bool, x ∈ L ↔ Alt (p.eval x.length) d true (fun ys => V (x :: ys))}

end AvgPHETH


