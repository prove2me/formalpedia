-- Prove2me | Definitions.Def_DynSort_Supplement_PermanentExtremes
-- name    : DynSort_Supplement_PermanentExtremes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:38:42.826192+00:00
-- url     : https://prove2.me/theorems/0d274417-d9d4-4c53-83fd-43b83ac7f908
-- title:
--   Two permanent extreme elements
-- statement:
--   Section 8 of the paper assumes that the minimum and maximum values are two permanent elements that are never deleted. For an update sequence $\sigma$, **PermanentExtremes**$(\sigma)$ holds if there are reals $\ell\le h$ such that
--
--   1. the first two updates of $\sigma$ (as far as $\sigma$ reaches) insert $\ell$ and $h$, in either order;
--   2. every value inserted by $\sigma$ lies in $[\ell,h]$;
--   3. no update of $\sigma$ deletes element $0$ or element $1$ (the elements inserted by the first two updates).
--
--   Then, after every prefix of $\sigma$, the minimum and the maximum of the stored values are $\ell$ and $h$, so $\mathrm{OPT}=h-\ell$ throughout. The paper's normalization, values in $[0,1]$ with $0$ and $1$ present, is the case $\ell=0$, $h=1$. The predicate is closed under prefixes, so a guarantee stated for every such $\sigma$ holds after every update. It is the standing assumption of Theorems 4 and 45.
--
--   **Formalization Note** Elements are named by the index of the update that inserts them, so the two permanent elements are elements $0$ and $1$.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Remark after Claim 44, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_DynSort_OnlineAlg

namespace DynSort.Supplement

open DynSort

/-! # Two permanent extreme elements (§8)

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), Remark after Claim 44, p.38 (PDF p.40): "We
assume, as before, that the minimum and maximum values are represented by two permanent elements
that cannot be deleted. In particular, we may assume that all values lie in [0, 1] and that 0 and
1 remain present throughout the execution."

**Formalization Note.** Elements are named by the index of the update inserting them
(`DynSort.alive`), so the two permanent elements, present throughout the execution, are the
elements `0` and `1` inserted by the first two updates. `PermanentExtremes σ` says: for some
`lo ≤ hi`, the first two updates of `σ` (as far as `σ` reaches) insert `lo` and `hi`, in either
order; every value inserted by `σ` lies in `[lo, hi]`; and no update of `σ` deletes element `0` or
element `1`. The predicate is closed under prefixes, so a guarantee stated for every `σ` with
`PermanentExtremes σ` holds after every update. The paper's `[0, 1]` is the case `lo = 0`,
`hi = 1`.
-/

/-- **Permanent minimum and maximum** (Remark, p.38): the first two updates insert the extreme
values `lo ≤ hi` (in either order), every inserted value lies in `[lo, hi]`, and the elements `0`
and `1` are never deleted. -/
def PermanentExtremes (σ : List Update) : Prop :=
  ∃ lo hi : ℝ, lo ≤ hi ∧
    (σ.take 2 <+: [Update.insert lo, Update.insert hi] ∨
      σ.take 2 <+: [Update.insert hi, Update.insert lo]) ∧
    (∀ x : ℝ, Update.insert x ∈ σ → lo ≤ x ∧ x ≤ hi) ∧
    Update.delete 0 ∉ σ ∧ Update.delete 1 ∉ σ

end DynSort.Supplement


