-- Prove2me | Definitions.Def_RLCDiscrepancy_IsSmooth
-- name    : RLCDiscrepancy_IsSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:23.397209+00:00
-- url     : https://prove2.me/theorems/1bca7ef2-f5bf-4dfe-a1f9-f7b21220895d
-- title:
--   $(f,\Gamma,j)$-smooth construction sequence
-- statement:
--   Let $C_0,\dots,C_k$ be a construction sequence, $f:\mathbb F_q^n\to\mathbb R_{\ge0}$, $\Gamma\ge 0$ and $0\le j\le k$. The sequence is **$(f,\Gamma,j)$-smooth** if
--
--   $$
--   |\delta_{C_i,f}|\le q^{k-i}\,\Gamma\qquad\text{for all } 0\le i\le j,
--   $$
--
--   and **$(f,\Gamma)$-smooth** if it is $(f,\Gamma,k)$-smooth. Smoothness asks that the deviation is small not only for the final code but along the whole construction, with a budget that shrinks by a factor $q$ per step.
--
--   **Formalization Note** The definition typechecks for all real $f$, $\Gamma$ and all $j$; the paper's ranges are met at every use. The exponent $k-i$ is a natural-number subtraction, exact since $i\le j\le k$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.2, p.25

import Mathlib
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_consSeq

namespace RLCDiscrepancy

/-- **(f, Γ, j)-smoothness** (Definition 4.2). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 4.2, p.25: "Fix a non-zero
function f : F^n_q → R≥0. A construction sequence C_0, …, C_k is (f, Γ, j)-smooth (for some real
Γ ≥ 0 and integer 0 ≤ j ≤ k) if |δ_{C_i,f}| ≤ q^{k−i} · Γ for all 0 ≤ i ≤ j. As a shorthand, we
write (f, Γ)-smooth to mean (f, Γ, k)-smooth."

**Formalization Note.** The sequence is given by its vectors `u` (see `consSeq`), and k is the
length of `u`. The definition typechecks for every real `f`, `Γ` and every `j`; the paper's
ranges (f ≥ 0 nonzero, Γ ≥ 0, j ≤ k) are met at every use. The exponent `k - i` is a natural
subtraction, exact because `i ≤ j ≤ k` at every use. (f, Γ)-smooth is `IsSmooth u f Γ k`. -/
def IsSmooth {F : Type*} [Field F] [Fintype F] {n k : ℕ} (u : Fin k → Fin n → F) (f : (Fin n → F) → ℝ) (Γ : ℝ)
    (j : ℕ) : Prop :=
  ∀ i ≤ j, |relDev (consSeq u i) f| ≤ (Fintype.card F : ℝ) ^ (k - i) * Γ

end RLCDiscrepancy


