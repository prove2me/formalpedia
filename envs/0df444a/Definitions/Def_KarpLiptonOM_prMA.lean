-- Prove2me | Definitions.Def_KarpLiptonOM_prMA
-- name    : KarpLiptonOM_prMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:49.574023+00:00
-- url     : https://prove2.me/theorems/5ce95f32-bd88-467d-b0aa-ff6434f72412
-- title:
--   prMA: promise Merlin–Arthur (Definition A.2.4)
-- statement:
--   A promise problem $\Pi$ is in $\mathrm{prMA}$ if there are a polynomial $s$ and a polynomial-time predicate $V$ such that for every $x$, with $y, r$ ranging over $\{0,1\}^{s(|x|)}$,
--   $$
--   x \in \Pi_{\mathrm{YES}} \Rightarrow \exists y \, \forall r \; V(x, y, r) = 1, \qquad
--   x \in \Pi_{\mathrm{NO}} \Rightarrow \forall y \; \Pr_r[V(x, y, r) = 1] < \tfrac14 .
--   $$
--   Merlin sends the proof $y$; Arthur checks it with random string $r$. Perfect completeness and soundness $1/4$ are without loss of generality.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.4, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_PolyPred3
import Definitions.Def_KarpLiptonOM_countStr

namespace KarpLiptonOM

/-- `Π ∈ prMA` (Definition A.2.4, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.21): a polynomial `s` and a polynomial-time `V` such that
for every `x`, with `y, r` ranging over `{0,1}^{s(|x|)}`: `x ∈ Π_YES ⇒ ∃y ∀r V(x, y, r) = 1` and
`x ∈ Π_NO ⇒ ∀y Pr_r[V(x, y, r) = 1] < 1/4`.

**Formalization Note** `Pr_r[V] < 1/4` is `4 · #{r : V} < 2^{s(|x|)}`. Perfect completeness and
soundness `1/4` are the paper's normalization (p.22, "without loss of generality [ZF87]"). -/
def prMA (PP : PromiseProblem) : Prop :=
  ∃ (s : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop), PolyPred3 V ∧
    ∀ x : List Bool,
      (x ∈ PP.yes → ∃ y : List Bool, y.length = s.eval x.length ∧
        ∀ r : List Bool, r.length = s.eval x.length → V x y r) ∧
      (x ∈ PP.no → ∀ y : List Bool, y.length = s.eval x.length →
        4 * countStr (s.eval x.length) (fun r => V x y r) < 2 ^ s.eval x.length)

end KarpLiptonOM


