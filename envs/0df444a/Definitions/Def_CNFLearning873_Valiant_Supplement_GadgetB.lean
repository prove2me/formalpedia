-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_GadgetB
-- name    : CNFLearning873_Valiant_Supplement_GadgetB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:04.159529+00:00
-- url     : https://prove2.me/theorems/555ca8dc-d497-43f7-8c6d-0c6bcd27fcc4
-- title:
--   Definition B.1 — restricted and unrestricted layered gadgets
-- statement:
--   Arrange $k\ell$ Boolean variables in $\ell$ layers of size $k$. Between layers $i$ and $i+1$, include one clause for each $j\in[k]$, on every variable of layer $i$ except $j$, together with variable $j$ of layer $i+1$. With printed layer indices starting at one, these clauses forbid all True when $i$ is odd and all False when $i$ is even. The restricted gadget additionally forbids all True on the first layer. The unrestricted gadget's actual number of satisfying assignments is $N_\ell$, and
--
--   $$\lambda_k=2^{k-1}-1+\sqrt{2^{k-1}(2^{k-1}-k)}.$$
--
--   The construction is the recalled Definition B.1, for integers $k\ge2$, $\ell\ge1$; the eigenvalue bound is stated separately for $k\ge3$. Variables in Lean are flattened to $\mathrm{Fin}(k\ell)$ with zero-based layer indices. The count is not defined by a recurrence or a desired estimate.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Definition B.1 and the notation before Lemma B.2, printed pp.35–36 = 1-based PDF pp.35–36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_CNF

noncomputable section

namespace CNFLearning873.Valiant.Supplement

/-- Definition B.1, pp.35-36 = PDF pp.35-36. Zero-based layer i corresponds to printed i+1. -/
def gadgetClause (k ℓ : ℕ) (i j : ℕ) : Clause (k * ℓ) :=
  fun v => if (v.val / k = i ∧ v.val % k ≠ j) ∨
      (v.val / k = i + 1 ∧ v.val % k = j) then some (i % 2 != 0) else none

def unrestrictedGadget (k ℓ : ℕ) : CNF (k * ℓ) := by
  classical
  exact ((Finset.range (ℓ - 1)).product (Finset.range k)).image
    (fun ij => gadgetClause k ℓ ij.1 ij.2)

def restrictedGadget (k ℓ : ℕ) : CNF (k * ℓ) := by
  classical
  exact insert (fun v => if v.val < k then some false else none) (unrestrictedGadget k ℓ)

def gadgetCount (k ℓ : ℕ) : ℕ := (solutions (unrestrictedGadget k ℓ)).card

def eigenvalue (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (k - 1) - 1 +
    Real.sqrt ((2 : ℝ) ^ (k - 1) * ((2 : ℝ) ^ (k - 1) - k))

end CNFLearning873.Valiant.Supplement


