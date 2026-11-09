-- Prove2me | Definitions.Def_GoodQLTC_IsLocallyMinimal
-- name    : GoodQLTC_IsLocallyMinimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:51:40.975413+00:00
-- url     : https://prove2.me/theorems/6bc0f99f-f5b7-4894-bcd0-9d3c3fb01956
-- title:
--   Locally minimal cochain (Definition 8.1)
-- statement:
--   A cochain $x\in C^j$ is **locally minimal** if $|x+\delta^{j-1}y|_b\ge|x|_b$ for every vertex $v\in X(0)$ and every $y\in C^{j-1}$ with $\mathrm{supp}_b\,y\subseteq X_{\ge v}(j-1)$.
--
--   **Formalization Note** Used for $j\ge1$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Definition 8.1, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_GoodQLTC_cobdMat

namespace GoodQLTC

/-- A **locally minimal** cochain, Gay–Jeronimo, arXiv:2609.20780 (held version), Definition 8.1,
p.25: `x ∈ C^j` is locally minimal if `|x + δ^{j−1} y|_b ≥ |x|_b` for every vertex `v ∈ X(0)` and
every `y ∈ C^{j−1}` with `supp_b y ⊆ X_{≥v}(j − 1)`.

**Formalization Note.** Used for `j ≥ 1` (Theorem 8.2 has `1 ≤ j < t`). A cochain `y ∈ C^{j−1}`
is supported above `v` when each of its nonzero blocks sits on a face `f ≥ v`. -/
def IsLocallyMinimal {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) (j : ℕ)
    (x : Cochain φ Fs j F) : Prop :=
  ∀ v : X, fdim φ v = 0 → ∀ y : Cochain φ Fs (j - 1) F,
    (∀ p : Σ f : Face φ (j - 1), Fin (Fs.d f.1), y p ≠ 0 → v ≤ p.1.1) →
    blockWeight x ≤ blockWeight (x + (cobdMat φ Fs (j - 1) j).mulVec y)

end GoodQLTC


