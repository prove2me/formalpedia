-- Prove2me | Definitions.Def_KarpLiptonOM_SigmaP
-- name    : KarpLiptonOM_SigmaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:17.714833+00:00
-- url     : https://prove2.me/theorems/926e7975-1675-4da4-8039-7ba5cd20ba9b
-- title:
--   $\Sigma^{\mathrm P}_k$ by alternating quantifiers
-- statement:
--   For $k \ge 0$, a language $L$ is in $\Sigma^{\mathrm P}_k$ if there are a polynomial $p$ and a polynomial-time predicate $V$ such that for every $x$,
--   $$
--   x \in L \iff \exists y_1 \, \forall y_2 \, \exists y_3 \cdots Q_k y_k \; V(x, y_1, \dots, y_k), \qquad y_i \in \{0,1\}^{p(|x|)} .
--   $$
--   $\Sigma^{\mathrm P}_1 = \mathrm{NP}$ and $\Sigma^{\mathrm P}_0 = \mathrm P$.
--
--   **Formalization Note** The paper uses $\Sigma^{\mathrm P}_k$ without defining it; this is the standard quantifier characterization, equivalent to the oracle form $\mathrm{NP}^{\Sigma^{\mathrm P}_{k-1}}$ used in the proof of Lemma A.3.8.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3, p.23; Lemma A.3.8, p.27 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred
import Definitions.Def_KarpLiptonOM_Alt

namespace KarpLiptonOM

/-- `Σ_k^P` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b) uses it without definition, §A.2.3, p.23 and Lemma A.3.8, p.27): `L ∈ Σ_k^P` iff
there are a polynomial `p` and a polynomial-time `(k+1)`-ary predicate `V` with
`x ∈ L ↔ ∃y₁ ∀y₂ ⋯ V(x, y₁, …, y_k)`, every `yᵢ ∈ {0,1}^{p(|x|)}`.

**Formalization Note** The Stockmeyer–Wrathall quantifier form; it equals the oracle form
`NP^{Σ_{k−1}^P}` used in the proof of Lemma A.3.8. `Σ_0^P = P`. -/
def SigmaP (k : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (V : List (List Bool) → Prop), PolyPred (k + 1) V ∧
    ∀ x : List Bool, x ∈ L ↔ Alt (p.eval x.length) k true (fun ys => V (x :: ys))}

end KarpLiptonOM


