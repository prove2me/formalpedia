-- Prove2me | Definitions.Def_DynLZ77_KK_SyncConstruction
-- name    : DynLZ77_KK_SyncConstruction
-- status  : Definition
-- author  : @shaygo
-- created : 2026-11-25T05:05:35.009948+00:00
-- url     : https://prove2.me/theorems/6f2ae4f4-2c1e-47ac-8a2a-f5f69f23445b
-- title:
--   Construction 8.1 of Kempa–Kociumaka: synchronizing sets from an identifier of length-$\tau$ fragments
-- statement:
--   Let $T=T[1..n]$ be a string and $\tau\ge 1$, and let
--   $$
--   Q=\{\,j:\ \mathrm{per}(T[j..j+\tau))\le \tau/3\,\}
--   $$
--   be the positions whose length-$\tau$ fragment has a period of at most $\tau/3$. For an identifier $\mathrm{id}$ that assigns a natural number to every string, Construction 8.1 of Kempa and Kociumaka is
--   $$
--   S_{\mathrm{id}}=\Bigl\{\,i\in[1..n-2\tau+1]:\ \min_{j\in[i..i+\tau]\setminus Q}\mathrm{id}\bigl(T[j..j+\tau)\bigr)\in\bigl\{\mathrm{id}(T[i..i+\tau)),\ \mathrm{id}(T[i+\tau..i+2\tau))\bigr\}\,\Bigr\},
--   $$
--   where $i\notin S_{\mathrm{id}}$ when $[i..i+\tau]\subseteq Q$ (the minimum is over the empty set).
--
--   By Lemma 8.2 of the source, $S_{\mathrm{id}}$ is a $\tau$-synchronizing set of $T$ for every identifier, and by Fact 8.9 a suitable identifier makes it of size $O(n/\tau)$.
--
--   **Formalization Note.** `InQ T τ j` is $j\in Q$, with the comparison taken over the reals. `syncSet T τ id` is $S_{\mathrm{id}}$, with the minimum written as "the fragment at $i$ (resp. $i+\tau$) is outside $Q$ and its identifier is at most that of every fragment starting in $[i..i+\tau]\setminus Q$". The identifier is any function on strings applied to the fragments, so equal fragments get equal identifiers, as for the class identifiers of the paper. Strings, 1-based positions, `sub` and `per` are those of `DynLZ77_Main_Strings` and `DynLZ77_Main_Structure`.
-- source:
--   D. Kempa, T. Kociumaka, String Synchronizing Sets: Sublinear-Time BWT Construction and Optimal LCE Data Structure, STOC 2019, https://arxiv.org/abs/1904.04228 (v2), Section 8, Construction 8.1 (with Lemma 8.2 and Fact 8.9)

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

/-!
# The Kempa–Kociumaka construction of synchronizing sets

D. Kempa, T. Kociumaka, *String Synchronizing Sets: Sublinear-Time BWT Construction and Optimal
LCE Data Structure*, STOC 2019, arXiv:1904.04228 (v2), Section 8, Construction 8.1.

**Formalization Note.** Strings, 1-based positions, `sub T i j = T[i..j]` and `per` (smallest
period) are those of `Def_DynLZ77_Main_Strings` / `Def_DynLZ77_Main_Structure`.
* `InQ T τ j`: `j ∈ Q`, i.e. `per(T[j..j+τ)) ≤ τ/3` (over the reals).
* `syncSet T τ id`: Construction 8.1 for an identifier `id` of length-`τ` fragments:
  `i ∈ [1..n − 2τ + 1]` is in the set iff the minimum of `id` over the fragments starting in
  `[i..i+τ] ∖ Q` is attained by the fragment at `i` or at `i + τ`. When `[i..i+τ] ⊆ Q` the
  minimum is over the empty set and `i` is not in the set (the convention of the proof of
  Lemma 8.2). In the paper `id` is a class identifier (`id(i) = id(j)` iff
  `T[i..i+τ) = T[j..j+τ)`); here `id` is any function on strings, applied to the fragments, so
  equal fragments automatically get equal identifiers.
-/

namespace DynLZ77.KK

open DynLZ77.Main

variable {α : Type}

/-- `j ∈ Q`: the length-`τ` fragment `T[j..j+τ)` has period at most `τ/3`. -/
def InQ (T : List α) (τ j : ℕ) : Prop :=
  ((per (sub T j (j + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3)

open Classical in
/-- Construction 8.1 of [KK19] with identifier `id`: `i ∈ [1..n − 2τ + 1]` such that the minimum
identifier over the fragments starting in `[i..i+τ] ∖ Q` is that of `T[i..i+τ)` or of
`T[i+τ..i+2τ)`. -/
noncomputable def syncSet (T : List α) (τ : ℕ) (id : List α → ℕ) : Finset ℕ :=
  (Finset.Icc 1 (T.length + 1 - 2 * τ)).filter fun i =>
    (¬ InQ T τ i ∧ ∀ j ∈ Finset.Icc i (i + τ), ¬ InQ T τ j →
        id (sub T i (i + τ - 1)) ≤ id (sub T j (j + τ - 1))) ∨
    (¬ InQ T τ (i + τ) ∧ ∀ j ∈ Finset.Icc i (i + τ), ¬ InQ T τ j →
        id (sub T (i + τ) (i + 2 * τ - 1)) ≤ id (sub T j (j + τ - 1)))

end DynLZ77.KK


