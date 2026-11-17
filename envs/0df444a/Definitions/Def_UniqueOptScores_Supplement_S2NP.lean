-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_S2NP
-- name    : UniqueOptScores_Supplement_S2NP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:53:22.414643+00:00
-- url     : https://prove2.me/theorems/a21193e1-8e95-484e-b894-7a7a550215ed
-- title:
--   The class $\mathrm S_2^{\mathrm{NP}}$ of symmetric alternation with an NP oracle
-- statement:
--   A language $L$ belongs to $\mathrm S_2^{\mathrm{NP}}$ if there are a polynomial $p$ and a Boolean predicate $R$ computable in $\mathrm P^{\mathrm{NP}}$ such that for every $x$
--   $$x\in L\iff \exists y\,\forall z\;R(x,y,z)=1,\qquad x\notin L\iff \exists z\,\forall y\;R(x,y,z)=0,$$
--   where $y,z\in\{0,1\}^{p(|x|)}$. On either side there is a certificate that prevails against every opposing certificate under the same predicate.
--
--   The paper uses the standard containment $\mathrm S_2^{\mathrm{NP}}\subseteq\Sigma^{\mathrm P}_3\cap\Pi^{\mathrm P}_3\subseteq\mathrm{PH}$, so $\mathrm{PH}=\mathrm S_2^{\mathrm{NP}}$ is a collapse of the polynomial hierarchy.
--
--   **Formalization Note** The predicate $R$ is given by the language of encoded triples $\langle x,\langle y,z\rangle\rangle$ on which $R=1$, which must lie in $\mathrm P^{\mathrm{NP}}$; all other triples have $R=0$. One polynomial and one predicate serve both conditions.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15), "Advice and symmetric alternation"

import Mathlib
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_UniqueOptScores_Supplement_PNP

namespace UniqueOptScores

namespace Supplement

/-- **The class S^NP_2 (symmetric alternation with an NP oracle).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15): "A language L belongs to S^NP_2 if there are a polynomial p and a
Boolean predicate R computable in P^NP such that x ∈ L ⇐⇒ ∃y ∀z R(x, y, z) = 1,
x ∉ L ⇐⇒ ∃z ∀y R(x, y, z) = 0, where y, z ∈ {0, 1}^{p(|x|)}."

`L ∈ S2NP` if there are a polynomial `p` and a language `R ∈ P^NP` of encoded triples
`⟨x, ⟨y, z⟩⟩` (the triples with `R(x, y, z) = 1`) such that both displayed equivalences hold for
every `x`, with `y` and `z` ranging over `{0,1}^{p(|x|)}`.

**Formalization Note.** "A Boolean predicate R computable in P^NP" is the language of triples on
which `R = 1`, required to lie in this supplement's `PNP` (adaptive queries to an NP language,
clock valid for every oracle); triples outside it have `R = 0`. The triple is `pair x (pair y z)`
with the base `pair`. One `p` and one `R` serve both conditions. -/
def S2NP : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ), ∃ R ∈ PNP, ∀ x : List Bool,
      (x ∈ L ↔ ∃ y : List Bool, y.length = p.eval x.length ∧
        ∀ z : List Bool, z.length = p.eval x.length → pair x (pair y z) ∈ R) ∧
      (x ∉ L ↔ ∃ z : List Bool, z.length = p.eval x.length ∧
        ∀ y : List Bool, y.length = p.eval x.length → pair x (pair y z) ∉ R)}

end Supplement

end UniqueOptScores


