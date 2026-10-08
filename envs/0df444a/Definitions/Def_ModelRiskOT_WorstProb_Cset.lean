-- Prove2me | Definitions.Def_ModelRiskOT_WorstProb_Cset
-- name    : ModelRiskOT_WorstProb_Cset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:02:03.612953+00:00
-- url     : https://prove2.me/theorems/b6ef135e-cd83-4fb4-8815-ae7ee9f49da4
-- title:
--   The sets $C_n = C_n^{(1)} \cup C_n^{(2)}$ of §2.4.1
-- statement:
--   Let $c$ satisfy (A1), let $A \subseteq S$, $\lambda^* \ge 0$ and $n > 1$. The paper defines $C_n := C_n^{(1)} \cup C_n^{(2)}$ with
--   $$C_n^{(1)} := \Big\{(x,y) \in S \times S : c(x,A) \le \tfrac{1}{\lambda^*}\big(1 + \tfrac1n\big),\ y \in A,\ c(x,y) < c(x,A) + \tfrac{1}{\lambda^* n}\Big\},$$
--   $$C_n^{(2)} := \Big\{(x,y) \in S \times S : c(x,A) > \tfrac{1}{\lambda^*}\big(1 - \tfrac1n\big),\ y \notin A,\ c(x,y) < \tfrac{1}{\lambda^* n}\Big\},$$
--   with the convention that $C_n^{(1)} = S \times A$ and $C_n^{(2)} = \emptyset$ when $\lambda^* = 0$.
--
--   $C_n$ collects the pairs $(x,y)$ that are nearly optimal moves for the inner problem $\sup_y\{1_A(y) - \lambda^* c(x,y)\}$: either $y$ is a near-closest point of $A$ for an $x$ within the inflated set, or $y$ is essentially $x$ itself for an $x$ outside it. Lemma 4 builds near-optimal transport plans concentrated on $C_n$.
--
--   **Formalization Note** Every inequality is multiplied through by $\lambda^* \ge 0$: $C_n^{(1)} = \{\lambda^* c(x,A) \le 1 + 1/n,\ y \in A,\ \lambda^* c(x,y) < \lambda^* c(x,A) + 1/n\}$ and $C_n^{(2)} = \{\lambda^* c(x,A) > 1 - 1/n,\ y \notin A,\ \lambda^* c(x,y) < 1/n\}$. For $\lambda^* > 0$ these are the printed sets; at $\lambda^* = 0$ and $n > 1$ they give exactly $S \times A$ and $\emptyset$, the paper's stated convention (checked in a sorry-free lemma). The index $n$ is a natural number; the sets are only used for $n > 1$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 11, §2.4.1, definition of C_n

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

namespace ModelRiskOT.WorstProb

/-- The set `C_n^{(1)}` of §2.4.1, p. 11:
`{(x, y) : c(x, A) ≤ (1/λ*)(1 + 1/n), y ∈ A, c(x, y) < c(x, A) + 1/(λ* n)}`, written with every
inequality multiplied through by `λ* ≥ 0`:
`λ* c(x, A) ≤ 1 + 1/n`, `y ∈ A`, `λ* c(x, y) < λ* c(x, A) + 1/n`.
For `λ* > 0` this is the printed set. At `λ* = 0` it is `S × A` (for `n ≥ 1`), the paper's stated
convention ("C_n^{(1)} = S × A … when λ* = 0"). -/
def Cset1 {S : Type*} (c : S → S → ℝ) (A : Set S) (lamStar : ℝ) (n : ℕ) : Set (S × S) :=
  {p | lamStar * costToSet c A p.1 ≤ 1 + 1 / (n : ℝ) ∧ p.2 ∈ A ∧
    lamStar * c p.1 p.2 < lamStar * costToSet c A p.1 + 1 / (n : ℝ)}

/-- The set `C_n^{(2)}` of §2.4.1, p. 11:
`{(x, y) : c(x, A) > (1/λ*)(1 − 1/n), y ∉ A, c(x, y) < 1/(λ* n)}`, in multiplied form:
`λ* c(x, A) > 1 − 1/n`, `y ∉ A`, `λ* c(x, y) < 1/n`.
For `λ* > 0` this is the printed set. At `λ* = 0` it is empty for `n > 1` (`0 > 1 − 1/n` fails),
the paper's stated convention ("C_n^{(2)} = ∅ … when λ* = 0"). -/
def Cset2 {S : Type*} (c : S → S → ℝ) (A : Set S) (lamStar : ℝ) (n : ℕ) : Set (S × S) :=
  {p | 1 - 1 / (n : ℝ) < lamStar * costToSet c A p.1 ∧ p.2 ∉ A ∧
    lamStar * c p.1 p.2 < 1 / (n : ℝ)}

/-- `C_n := C_n^{(1)} ∪ C_n^{(2)}` (§2.4.1, p. 11), for `λ* ≥ 0` and `n > 1`. -/
def Cset {S : Type*} (c : S → S → ℝ) (A : Set S) (lamStar : ℝ) (n : ℕ) : Set (S × S) :=
  Cset1 c A lamStar n ∪ Cset2 c A lamStar n

end ModelRiskOT.WorstProb


