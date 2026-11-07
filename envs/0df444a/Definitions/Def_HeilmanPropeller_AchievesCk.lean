-- Prove2me | Definitions.Def_HeilmanPropeller_AchievesCk
-- name    : HeilmanPropeller_AchievesCk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:28.200429+00:00
-- url     : https://prove2.me/theorems/751a8aa2-00e8-4039-a2eb-09a6237ffd38
-- title:
--   A Gaussian partition achieving $C_k$
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition $\mathcal A=(A_1,\dots,A_k)$ of $\mathbb R^d$ write $z_i=\int_{A_i}x\,d\gamma_d(x)$ and $F(\mathcal A)=\sum_{i=1}^k\|z_i\|^2$, and let
--
--   $$C_k=\sup_{n\ge 1}\ \sup_{\mathcal B}F(\mathcal B),$$
--
--   the supremum over all partitions $\mathcal B$ of $\mathbb R^n$ into $k$ measurable sets, over all dimensions $n$.
--
--   The partition $\mathcal A$ **achieves $C_k$** when $F(\mathcal B)\le F(\mathcal A)$ for every partition $\mathcal B$ of every $\mathbb R^n$ into $k$ sets; then $F(\mathcal A)=C_k$. This is the hypothesis "$\mathcal A$ achieves the supremum in the definition of $C_k$" (equivalently "$F(\mathcal A)=C_k$") of Lemmas 2.3, 5.1, 5.2, 6.1 and 7.1 of the paper.
--
--   **Formalization Note** Partitions are almost-everywhere partitions (measurable cells, almost every point in exactly one cell), from the reused block `OAI.GaussianPropeller`; a null modification changes no moment, so the supremum is the same as over exact partitions. Competitors range over every dimension, including $n=0$, where every partition has value $0$. The supremum is encoded as "$F(\mathcal A)$ is an upper bound", so no real supremum with a junk value is used.
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), display (1.1), p.1; "achieves the supremum in the definition of C_k", Lemma 5.1, p.8

import Mathlib
import Definitions.Def_GaussianPropeller

namespace HeilmanPropeller

open OAI.GaussianPropeller

/-- **A partition achieving `C_k`.** Heilman, *On the Propeller Conjecture*, arXiv:2610.32158
(held version, sha256 13f5ddf8…), display (1.1), p.1, and the phrase "achieves the supremum in the
definition of `C_k`" (Lemmas 5.1, 5.2, p.8–9; "`F(A) = C_k`", Lemma 2.3, p.5, Section 6, p.11,
Lemma 7.1, p.13).

A family `A = (A₁, …, A_k)` of subsets of `ℝᵈ` achieves `C_k` when it is a partition and its value
`F(A) = ∑ᵢ ‖∫_{Aᵢ} x dγ_d(x)‖²` is at least the value of every partition of every `ℝⁿ` into `k`
sets. Then `F(A) = C_k := sup_{n ≥ 1} sup_B F(B)`.

**Formalization Note.**
* `IsPartition` (from the reused block `OAI.GaussianPropeller`) asks for measurable cells such that
  `γ`-almost every point lies in exactly one cell. A null modification changes no moment, so the
  supremum over these a.e.-partitions equals the paper's supremum over exact partitions.
* Competitors range over every dimension `n`, as in `C_k = sup_{n ≥ 1} sup_B F(B)`. Including
  `n = 0` changes nothing: `ℝ⁰` is a point and every partition of it has value `0`.
* The supremum is written as "`value A` is an upper bound", so no real `sSup` (with its junk value on
  unbounded sets) is used; `C_k` is then `value A`. -/
def AchievesCk {d k : ℕ} (A : Fin k → Set (Space d)) : Prop :=
  IsPartition A ∧ ∀ (n : ℕ) (B : Fin k → Set (Space n)), IsPartition B → value B ≤ value A

end HeilmanPropeller


