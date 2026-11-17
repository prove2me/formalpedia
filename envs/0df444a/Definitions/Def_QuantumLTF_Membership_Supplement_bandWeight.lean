-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
-- name    : QuantumLTF_Membership_Supplement_bandWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:37:35.349206+00:00
-- url     : https://prove2.me/theorems/0c2279a8-080e-4582-a128-f8a8c96bc1c5
-- title:
--   Band weight $p_K=\|\Pi_{B_K}|F_w\rangle\|^2$
-- statement:
--   With the degree band $B_K=\{K,\dots,2K\}$ and $|\alpha|=\alpha_1+\dots+\alpha_n$,
--   $$p_K=\|\Pi_{B_K}|F_w\rangle\|^2=\sum_{K\le|\alpha|\le 2K}\widehat f_w(\alpha)^2 .$$
--
--   **Formalization Note** Every $\alpha$ with $|\alpha|\le2K$ has $\alpha_i\le2K$, so the sum is finite. By rotation invariance $p_K$ does not depend on the unit vector $w$, but it is defined from $\widehat f_w$ as printed.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eqs. (167)–(169), p. 63 (PDF p. 64); Theorem 5.3

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff

namespace QuantumLTF.Membership.Supplement

/-- **`p_K := ‖Π_{B_K}|F_w⟩‖²`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Eqs. (167)–(169), p. 63 (PDF p. 64), and Theorem 5.3:
`B_K := {K, …, 2K}`, `Π_{B_K} := Σ_{k ∈ B_K} Σ_{|α| = k} |α⟩⟨α|` with `|α| = α_1 + ⋯ + α_n`, so
`p_K = Σ_{K ≤ |α| ≤ 2K} f̂_w(α)²`.

**Formalization Note.** Every `α` with `|α| ≤ 2K` has `α_i ≤ 2K`, so the sum runs over
`α : Fin n → Fin (2K + 1)`, a finite set. `p_K` does not depend on `w` (p. 63, Eq. (169)), but it is
defined from `f̂_w` as printed. -/
noncomputable def bandWeight {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (K : ℕ) : ℝ :=
  ∑ α : Fin n → Fin (2 * K + 1),
    if K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K then hermCoeff w (fun i => (α i : ℕ)) ^ 2 else 0

end QuantumLTF.Membership.Supplement


