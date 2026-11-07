-- Prove2me | Definitions.Def_KarpLiptonOM_sOprMA
-- name    : KarpLiptonOM_sOprMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:59.852568+00:00
-- url     : https://prove2.me/theorems/668e5919-f3fd-40cb-99ed-888f0dd67656
-- title:
--   sOprMA: strict oblivious promise Merlin–Arthur (Definition A.2.4)
-- statement:
--   A promise problem $\Pi$ is in $\mathrm{sOprMA}$ (strict OprMA) if there are a polynomial $s$, a polynomial-time predicate $V$ and strings $y_n \in \{0,1\}^{s(n)}$, the **oblivious proofs**, such that for every $n$ and every $x \in \{0,1\}^n$, with $y, r$ ranging over $\{0,1\}^{s(n)}$:
--
--   1. (OMA1) $x \in \Pi_{\mathrm{YES}} \Rightarrow \forall r\; V(x, y_n, r) = 1$;
--   2. (OMA2) $x \in \Pi_{\mathrm{NO}} \Rightarrow \forall y\; \Pr_r[V(x, y, r) = 1] < \tfrac14$;
--   3. (OMA4) $\forall y\, \forall r\; \bigl(V(x, y, r) = 1 \Rightarrow V(x, y_n, r) = 1\bigr)$.
--
--   Condition (OMA4) says that the oblivious proof dominates every other proof on every input and every random string. sOprMA is the oracle class of the generators of OM.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.4, pp.21–22

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_PolyPred3
import Definitions.Def_KarpLiptonOM_countStr

namespace KarpLiptonOM

/-- `Π ∈ sOprMA` (strict OprMA; Definition A.2.4, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), pp.21–22): a polynomial `s`, a
polynomial-time `V` and **oblivious proofs** `y_n ∈ {0,1}^{s(n)}` such that for every `x ∈ {0,1}ⁿ`,
with `y, r` ranging over `{0,1}^{s(n)}`:
(OMA1) `x ∈ Π_YES ⇒ ∀r V(x, y_n, r) = 1`;
(OMA2) `x ∈ Π_NO ⇒ ∀y Pr_r[V(x, y, r) = 1] < 1/4`;
(OMA4) `∀y ∀r (V(x, y, r) = 1 ⇒ V(x, y_n, r) = 1)`. -/
def sOprMA (PP : PromiseProblem) : Prop :=
  ∃ (s : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop) (y : ℕ → List Bool),
    PolyPred3 V ∧ (∀ n, (y n).length = s.eval n) ∧ ∀ x : List Bool,
      (x ∈ PP.yes → ∀ r : List Bool, r.length = s.eval x.length → V x (y x.length) r) ∧
      (x ∈ PP.no → ∀ y' : List Bool, y'.length = s.eval x.length →
        4 * countStr (s.eval x.length) (fun r => V x y' r) < 2 ^ s.eval x.length) ∧
      (∀ y' r : List Bool, y'.length = s.eval x.length → r.length = s.eval x.length →
        V x y' r → V x (y x.length) r)

end KarpLiptonOM


