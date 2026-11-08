-- Prove2me | Definitions.Def_ValiantModel_Guarantee
-- name    : ValiantModel_Guarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:04.607058+00:00
-- url     : https://prove2.me/theorems/2b5aae53-cd81-4e95-ae7d-29062974505a
-- title:
--   Budget per oracle and the Valiant guarantee at one input $(d,\varepsilon,\delta)$
-- statement:
--   A randomized protocol $P$ on $\{0,1\}^d$ is **within budget $B$** if every deterministic protocol in its support makes at most $B$ example calls and at most $B$ membership queries on every path.
--
--   $P$ meets the **Valiant guarantee** for a class $H_d$ at $(\varepsilon,\delta)$ if, for every target $h\in H_d$ and every distribution $D$ compatible with $h$, with probability at least $1-\delta$ over the samples and the internal randomness, the output $g$ satisfies
--
--   $$
--   \mathrm{supp}(g)\subseteq\mathrm{supp}(h)\qquad\text{and}\qquad \Pr_{x\sim D}\bigl(x\notin\mathrm{supp}(g)\bigr)\le\varepsilon .
--   $$
--
--   Stating the guarantee at one input lets Lemma B.1 and Theorem 4.4 state their restricted parameter ranges.
--
--   **Formalization Note** The bound is `ENNReal.ofReal (1 - δ)`, which is the true value $1-\delta$ for $\delta\le 1$; every use has $0<\delta<1$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.1 (PDF p.3), Definition 1; p.15 (PDF p.17), Remark 3.1

import Mathlib
import Definitions.Def_ValiantModel_Compatible
import Definitions.Def_ValiantModel_MeetsValiant
import Definitions.Def_ValiantModel_runLaw

namespace ValiantModel

/-- The sample/query budget of Definition 1, counted per oracle as in Remark 3.1
(arXiv:2605.13840, version held, p.15, PDF p.17) and the proof of Theorem 4.10 (p.28, PDF p.30):
every protocol in the support makes at most `B` example-oracle calls and at most `B` membership
queries on every path. -/
def WithinBudget {d : ℕ} (P : PMF (Protocol d)) (B : ℝ) : Prop :=
  ∀ p ∈ P.support, (p.exampleDepth : ℝ) ≤ B ∧ (p.queryDepth : ℝ) ≤ B

/-- **The Valiant guarantee** of Definition 1, arXiv:2605.13840 (version held), p.1 (PDF p.3), for
one input `(d, ε, δ)`: for every target `h ∈ Hd` and every distribution `D` compatible with `h`,
with probability at least `1 - δ` over the samples and the internal randomness the output meets the
conclusions of Definition 1.

**Formalization Note.** `ENNReal.ofReal (1 - δ)` is the true value `1 - δ` for `δ ≤ 1`; every use
has `0 < δ < 1`. -/
def Guarantee {d : ℕ} (Hd : Set (Hypothesis d)) (P : PMF (Protocol d)) (ε δ : ℝ) : Prop :=
  ∀ h ∈ Hd, ∀ D : PMF (Point d), Compatible D h →
    ENNReal.ofReal (1 - δ) ≤
      (runLaw P h D).toOuterMeasure {o | MeetsValiant h D ε o.output}

end ValiantModel


