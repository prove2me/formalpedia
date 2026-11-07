-- Prove2me | Definitions.Def_CallCountPOPBR_Instance
-- name    : CallCountPOPBR_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:19.785804+00:00
-- url     : https://prove2.me/theorems/c3a041b0-3c33-41f7-aa87-5276f445f79d
-- title:
--   A POPBR instance $(N,d,p,\mathrm{Obs})$
-- statement:
--   An instance of **Partial-Observation Periodic Binary Reconstruction** (POPBR) consists of a horizon $N$, a base-case threshold (window) $d$, a period $p$, and a partial map
--   $$
--   \mathrm{Obs}:\{0,\dots,N\}\rightharpoonup\mathbb Z_{>0}
--   $$
--   recording the observed entries of a call-count sequence $C_0,\dots,C_N$.
--
--   This is the input object of every result in the mission.
--
--   **Formalization Note** $\mathrm{Obs}$ is stored as a list of entries, entry $n$ being `none` (the blank symbol: $C_n$ unobserved) or `some v` ($C_n$ observed to equal $v$), as in the paper's encoding. The side conditions are the separate predicate `Instance.IsValid`.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Definition 2.1, p.4

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **A POPBR instance** (Definition 2.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Definition 2.1, p.4:
"An instance consists of positive integers N, d, p with 1 ≤ d ≤ N and 1 ≤ p ≤ N + 1, and a
partial map Obs : {0, …, N} ⇀ ℤ_{>0}."

The fields are the horizon `N`, the base-case threshold (window) `d`, the period `p`, and the
observation list `obs`, whose entry `n` is `none` (the blank symbol: `C_n` unobserved) or
`some v` (`C_n` observed to equal `v`).

**Formalization Note.** The partial map `Obs` is the list of its `N + 1` entries, exactly as the
paper encodes it ("a list of N + 1 entries, each either a blank symbol or an observed integer").
The side conditions (`1 ≤ d ≤ N`, `1 ≤ p ≤ N + 1`, list length `N + 1`, observed values
positive) are `Instance.IsValid`. -/
structure Instance where
  /-- The horizon `N`: the sequence is `C_0, …, C_N`. -/
  N : ℕ
  /-- The base-case threshold and window `d`. -/
  d : ℕ
  /-- The period `p` of the branching rule. -/
  p : ℕ
  /-- The observations: entry `n` is `none` (blank) or `some (Obs n)`. -/
  obs : List (Option ℕ)

end CallCountPOPBR


