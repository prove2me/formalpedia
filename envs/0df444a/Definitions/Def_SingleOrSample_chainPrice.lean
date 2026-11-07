-- Prove2me | Definitions.Def_SingleOrSample_chainPrice
-- name    : SingleOrSample_chainPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:43.447935+00:00
-- url     : https://prove2.me/theorems/91fc5474-f1f0-4d95-a680-2049813c71f1
-- title:
--   Supporting prices $w_e=a_e/v(P_h)$
-- statement:
--   Let $(P_1,\dots,P_n)$ be a partition of the goods, given as a labelling, and fix an ordering $g_{h,1},\dots,g_{h,\ell_h}$ of each bundle. The **chain marginal** of $g_{h,s}$ is
--   $$a_{g_{h,s}}=v\bigl(g_{h,s}\mid\{g_{h,1},\dots,g_{h,s-1}\}\bigr),$$
--   and the **supporting price** of $e\in P_h$ is $w_e=a_e/v(P_h)$. The prices split one unit of weight across each bundle, in a way that lower-bounds the value of every subset of it. This is what lets an exponential-moment bound for an additive function control a submodular one.
--
--   **Formalization Note** As in `LittleCharity.MMS.mms`, partitions are labellings `Fin m → Fin n`, so bundles may be empty. Statements assume $v(P_h)\ge1$, so no division by zero occurs in them.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), §4.2.2, p.15

import Mathlib

namespace SingleOrSample

/-- The MMS bundle `P_h` of a labelling `P` of the goods. -/
def bundle {m n : ℕ} (P : Fin m → Fin n) (h : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => P e = h

/-- The chain marginal `a_e = v(e | goods before e)` along an ordering `l` of a bundle (Chawla, Huang,
Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027
submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, §4.2.2, p.15). -/
def chainMarginal {m : ℕ} (v : Finset (Fin m) → ℝ) (l : List (Fin m)) (e : Fin m) : ℝ :=
  v ((l.takeWhile (· ≠ e)).toFinset ∪ {e}) - v (l.takeWhile (· ≠ e)).toFinset

/-- The **supporting price** `w_e = a_e / v(P_h)` of `e ∈ P_h` (§4.2.2, p.15), for a labelling `P` and an
ordering `order h` of each bundle.

**Formalization Note.** The partition is a labelling `Fin m → Fin n`, as in `LittleCharity.MMS.mms`, so
empty bundles are allowed; the division is harmless because statements assume `1 ≤ v(P_h)`, which is
what `MMS = 1` gives for an MMS-defining partition. -/
noncomputable def chainPrice {m n : ℕ} (v : Finset (Fin m) → ℝ) (P : Fin m → Fin n)
    (order : Fin n → List (Fin m)) (e : Fin m) : ℝ :=
  chainMarginal v (order (P e)) e / v (bundle P (P e))

end SingleOrSample


