-- Prove2me | Definitions.Def_ModularCurve_PlaceWidthChar
-- name    : ModularCurve_PlaceWidthChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/b53028c8-6a0d-5192-8a9e-18c6a13b4dfd
-- title:
--   Widths of j-invariants and places in small characteristic
-- statement:
--   Fix a field $K$ with decidable equality. For a natural number $q$ (to be read as the characteristic in which one works) and $j \in K$, `jWidthChar q j` is defined by a case table: if $q = 2$ it is $12$ when $j = 0$ and $1$ otherwise; if $q = 3$ it is $6$ when $j = 0$ and $1$ otherwise; for every other value of $q$, including $q = 0$, it is the tame width `jWidth j`, which is $3$ at $j = 0$, $2$ at $j = 1728$ (when $j \neq 0$) and $1$ elsewhere. The argument $q$ is a bare natural number, not tied by any hypothesis to the characteristic of $K$.
--
--   The second definition transports this to places of the level-$N$ modular function field. For $N \neq 0$ and a place $w$ of `modularFunctionFieldC K N` over $K$, `placeWidthChar q N w` is the truncating natural-number quotient of `jWidthChar q` evaluated at the residue $w$-value of the generator `jGeomGen K N` by `placeRamificationJ N w`, the latter being the non-negative part of the order at $w$ of `jGeomGen K N` minus the constant function with that residue value — the ramification index of the $j$-map at $w$. The shape is exactly that of the tame `placeWidth`, with `jWidth` replaced by `jWidthChar q`.
--
--   The accompanying lemmas record: agreement of `jWidthChar q` with `jWidth` whenever $q \neq 2$ and $q \neq 3$, in particular for $5 \le q$ and for $q = 0$; the values $12$, $6$ and $1$ in the wild cases; that every value is one of `jWidth j`, $1$, $6$, $12$, hence positive and a divisor of $12$; invariance under any ring homomorphism $f : K \to L$ of fields, $\mathrm{jWidthChar}\,q\,(f j) = \mathrm{jWidthChar}\,q\,j$; the quotient formula for `placeWidthChar`; its agreement with `placeWidth` for $q \neq 2, 3$ and for $5 \le q$; and that it vanishes wherever the ramification index is $0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of these widths; both `jWidthChar` and `placeWidthChar` are the project's own numerical bookkeeping functions, built on the project's `Place` structure for function fields.
--
--   **Where it is used.** The widths attached to places of the modular function field serve in the description of the special fibre of the modular curve, where the places with supersingular $j$-invariant give the nodes and their widths depend on the order of the automorphism group of the corresponding elliptic curve; the characteristic-sensitive variant is what is needed when the residue characteristic is $2$ or $3$, where $j = 0$ and $j = 1728$ coincide and the automorphism groups are larger.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PlaceWidthChar.lean

import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

def jWidthChar {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else jWidth j

def placeWidthChar {K : Type*} [Field K] [DecidableEq K] (q N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  jWidthChar q (w.evalAt (jGeomGen K N)) / placeRamificationJ N w

theorem jWidthChar_of_ne {K : Type*} [Field K] [DecidableEq K] {q : ℕ}
    (h2 : q ≠ 2) (h3 : q ≠ 3) (j : K) : jWidthChar q j = jWidth j := by
  unfold jWidthChar
  rw [if_neg h2, if_neg h3]

theorem jWidthChar_of_five_le {K : Type*} [Field K] [DecidableEq K] {q : ℕ} (hq : 5 ≤ q) (j : K) :
    jWidthChar q j = jWidth j :=
  jWidthChar_of_ne (by omega) (by omega) j

theorem jWidthChar_zero_char {K : Type*} [Field K] [DecidableEq K] (j : K) :
    jWidthChar 0 j = jWidth j :=
  jWidthChar_of_ne (by decide) (by decide) j

theorem jWidthChar_two_of_eq_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j = 0) :
    jWidthChar 2 j = 12 := by
  unfold jWidthChar
  rw [if_pos rfl, if_pos h]

theorem jWidthChar_three_of_eq_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j = 0) :
    jWidthChar 3 j = 6 := by
  unfold jWidthChar
  rw [if_neg (by decide), if_pos rfl, if_pos h]

theorem jWidthChar_two_of_ne_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j ≠ 0) :
    jWidthChar 2 j = 1 := by
  unfold jWidthChar
  rw [if_pos rfl, if_neg h]

theorem jWidthChar_three_of_ne_zero {K : Type*} [Field K] [DecidableEq K] {j : K} (h : j ≠ 0) :
    jWidthChar 3 j = 1 := by
  unfold jWidthChar
  rw [if_neg (by decide), if_pos rfl, if_neg h]

theorem jWidthChar_eq_or {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) :
    jWidthChar q j = jWidth j ∨ jWidthChar q j = 1 ∨ jWidthChar q j = 6 ∨ jWidthChar q j = 12 := by
  unfold jWidthChar
  split_ifs <;> simp

theorem jWidthChar_pos {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) : 0 < jWidthChar q j := by
  rcases jWidthChar_eq_or q j with h | h | h | h <;> rw [h]
  · exact jWidth_pos j
  · exact (by decide : (0 : ℕ) < 1)
  · exact (by decide : (0 : ℕ) < 6)
  · exact (by decide : (0 : ℕ) < 12)

theorem jWidthChar_dvd_twelve {K : Type*} [Field K] [DecidableEq K] (q : ℕ) (j : K) :
    jWidthChar q j ∣ 12 := by
  rcases jWidthChar_eq_or q j with h | h | h | h
  · rw [h]
    exact (jWidth_dvd_six j).trans (by decide)
  · rw [h]
    exact (by decide : (1 : ℕ) ∣ 12)
  · rw [h]
    exact (by decide : (6 : ℕ) ∣ 12)
  · rw [h]

theorem jWidthChar_map {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
    (f : K →+* L) (q : ℕ) (j : K) : jWidthChar q (f j) = jWidthChar q j := by
  unfold jWidthChar
  rw [jWidth_map f j]
  by_cases hj0 : j = 0
  · subst hj0
    simp
  · have hne : f j ≠ 0 := (map_ne_zero_iff f f.injective).mpr hj0
    simp only [if_neg hj0, if_neg hne]

theorem placeWidthChar_of_ne {K : Type*} [Field K] [DecidableEq K] {q : ℕ}
    (h2 : q ≠ 2) (h3 : q ≠ 3) (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = placeWidth N w := by
  unfold placeWidthChar placeWidth
  rw [jWidthChar_of_ne h2 h3]

theorem placeWidthChar_of_five_le {K : Type*} [Field K] [DecidableEq K] {q : ℕ} (hq : 5 ≤ q)
    (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = placeWidth N w :=
  placeWidthChar_of_ne (by omega) (by omega) N w

theorem placeWidthChar_eq_div {K : Type*} [Field K] [DecidableEq K] (q N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) :
    placeWidthChar q N w = jWidthChar q (w.evalAt (jGeomGen K N)) / placeRamificationJ N w :=
  rfl

theorem placeWidthChar_of_placeRamificationJ_eq_zero {K : Type*} [Field K] [DecidableEq K] (q N : ℕ)
    [NeZero N] {w : Place K (modularFunctionFieldC K N)} (h : placeRamificationJ N w = 0) :
    placeWidthChar q N w = 0 := by
  unfold placeWidthChar
  rw [h, Nat.div_zero]

example : jWidthChar 2 (0 : ZMod 2) = 12 := jWidthChar_two_of_eq_zero rfl
example : jWidthChar 3 (0 : ZMod 3) = 6 := jWidthChar_three_of_eq_zero rfl
example : jWidthChar 3 (1 : ZMod 3) = 1 := jWidthChar_three_of_ne_zero one_ne_zero
example (j : ℚ) : jWidthChar 0 j = jWidth j := jWidthChar_zero_char j

end ModularCurve

end


