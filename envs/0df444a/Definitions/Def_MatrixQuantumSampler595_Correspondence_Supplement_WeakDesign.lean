-- Prove2me | Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_WeakDesign
-- name    : MatrixQuantumSampler595_Correspondence_Supplement_WeakDesign
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:46.183425+00:00
-- url     : https://prove2.me/theorems/75747c5e-177a-4ca7-8462-dd4a2c88b02f
-- title:
--   Definition 4.2 — weak designs
-- statement:
--   Let $v,M,\ell$ be natural numbers and $\varrho$ a real number. An ordered family $S_1,\ldots,S_M\subseteq[v]$ is an **$(\ell,\varrho)$ weak design** if
--
--   $$|S_i|=\ell\quad\text{and}\quad\sum_{j<i}2^{|S_i\cap S_j|}\le\varrho M\qquad(1\le i\le M).$$
--
--   The aggregate overlap budget controls all previous sets in their stated order. This is the design notion used in the multilinear extractor theorem, rather than an individual bound on every pairwise intersection.
--
--   **Formalization Note** Both coordinate and family indices start at zero in Lean. The sum is over the strictly earlier indices; for the first set it is empty.
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Definition 4.2, p.17

import Mathlib

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Definition 4.2 (p.17). No pairwise-intersection bound replaces the ordered sum. -/
def IsWeakDesign {v M : ℕ} (S : Fin M → Finset (Fin v)) (ell : ℕ) (rho : ℝ) : Prop :=
  (∀ i, (S i).card = ell) ∧
  ∀ i, (∑ j ∈ Finset.univ.filter (fun j : Fin M => j < i),
    (2 : ℝ) ^ ((S i ∩ S j).card)) ≤ rho * M

end MatrixQuantumSampler595.Correspondence.Supplement


