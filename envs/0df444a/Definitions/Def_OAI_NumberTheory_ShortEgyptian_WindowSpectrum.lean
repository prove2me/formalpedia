-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
-- name    : OAI_NumberTheory_ShortEgyptian_WindowSpectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:22:44.25166+00:00
-- url     : https://prove2.me/theorems/f4b3c475-3eea-4ced-bfb1-452e5effc9c4
-- title:
--   Initial windows of residues and the circular distance of a frequency from zero
-- statement:
--   Let $q$ and $L$ be natural numbers. For $q\ge 1$ and $x\in\mathbb{Z}/q\mathbb{Z}$, let $\bar x\in\{0,1,\dots,q-1\}$ denote the least nonnegative representative of $x$.
--
--   1. **Window.** The initial window of length $L$ is the image of $\{0,1,\dots,L-1\}$ under reduction modulo $q$:
--
--      $$W_q(L)=\{\,n \bmod q:\ 0\le n<L\,\}\subseteq\mathbb{Z}/q\mathbb{Z}.$$
--
--   2. **Size of a window.** If $L\le q$, reduction modulo $q$ is injective on $\{0,\dots,L-1\}$, and consequently $|W_q(L)|=L$.
--
--   3. **Frequency distance.** For a frequency $k\in\mathbb{Z}/q\mathbb{Z}$,
--
--      $$\|k\|_q=\min\bigl(\bar k,\ q-\bar k\bigr),$$
--
--      the distance from $k$ to $0$ along the cycle $\mathbb{Z}/q\mathbb{Z}$.
--
--   Windows are the target sets of the discrepancy argument: for $L\le q$, a residue lies in $W_q(L)$ exactly when its least nonnegative representative is less than $L$. Their character sums decay with the frequency distance: in the surrounding development it is shown that for $L,M\le q$ and $H\ge 1$, writing $S_A(k)=\sum_{a\in A}\exp(2\pi i k\bar a/q)$,
--
--   $$\sum_{k:\ \|k\|_q>H}|S_{W_q(L)}(k)|\,|S_{W_q(M)}(k)|\le\frac{2q^2}{H},$$
--
--   so only the frequencies with $\|k\|_q\le H$ need to be controlled.
--
--   **Formalization Note** The Lean names are `natWindow`, `natCast_injOn_range`, `natWindow_card` and `frequencyDistance`; the representative is `ZMod.val`. The frequency distance is defined for every q, but for q = 0 (where `ZMod 0` is the integers) truncated subtraction makes it identically 0; only q at least 1 is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowSpectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/WindowSpectrum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy

namespace OAI

universe uα uβ

namespace ShortEgyptian

open scoped BigOperators
open Finset

def natWindow (q L : ℕ) : Finset (ZMod q) := (Finset.range L).image Nat.cast

theorem natCast_injOn_range {q L : ℕ} (hL : L ≤ q) :
    Set.InjOn (Nat.cast : ℕ → ZMod q) (Finset.range L) := by
  intro a ha b hb heq
  have ha' : a < q := (Finset.mem_range.mp ha).trans_le hL
  have hb' : b < q := (Finset.mem_range.mp hb).trans_le hL
  have hh := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hh

@[simp] theorem natWindow_card {q L : ℕ} (hL : L ≤ q) : (natWindow q L).card = L := by
  rw [natWindow, Finset.card_image_of_injOn (natCast_injOn_range hL), Finset.card_range]

def frequencyDistance {q : ℕ} (k : ZMod q) : ℕ := min k.val (q - k.val)

end ShortEgyptian

end OAI


