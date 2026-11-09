-- Prove2me | Definitions.Def_SharpConsist_uA
-- name    : SharpConsist_uA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:35.96221+00:00
-- url     : https://prove2.me/theorems/010ccdbb-3526-4283-84b0-7083bf73962e
-- title:
--   The imbalance $u_A(S)$
-- statement:
--   Let $X=[n]$, $A\subseteq X$ (the hidden set) and $\bar A=X\setminus A$. The **imbalance** of $S\subseteq X$ is
--   $$u_A(S)=\frac{|S\cap A|-|S\cap\bar A|/m}{k}.$$
--   With $x=|S\cap A|/k$ and $y=|S\cap\bar A|/k$ this is $u=x-y/m$.
--
--   **Formalization Note.** Counts are cast to reals; every statement using $u_A$ assumes $k\ge1$ and $m\ge32$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15

import Mathlib

namespace SharpConsist

/-- The **imbalance** `u_A(S) = (|S ∩ A| − |S ∩ Ā|/m)/k` of a set `S ⊆ X` relative to the hidden set
`A ⊆ X`, `Ā = X \ A`. Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, p.15.

**Formalization Note.** `X = Fin n`; counts are cast to `ℝ`. Every statement that uses `u_A` assumes
`1 ≤ k` and `32 ≤ m`, so neither division is by zero. -/
noncomputable def uA {n : ℕ} (k m : ℕ) (A S : Finset (Fin n)) : ℝ :=
  (((S ∩ A).card : ℝ) - ((S ∩ Aᶜ).card : ℝ) / (m : ℝ)) / (k : ℝ)

end SharpConsist


