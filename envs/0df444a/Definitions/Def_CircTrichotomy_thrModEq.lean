-- Prove2me | Definitions.Def_CircTrichotomy_thrModEq
-- name    : CircTrichotomy_thrModEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:55.602215+00:00
-- url     : https://prove2.me/theorems/a39c785a-16f9-4abe-9e34-a37c30f0c08e
-- title:
--   Threshold congruences $\equiv_t$ and $\equiv^t_k$ on $\mathbb N$
-- statement:
--   For $t\in\mathbb N$, $m\equiv_t n$ if $m=n$ or $m,n\ge t$. For $k\ge1$, $m\equiv^t_k n$ if $m=n$, or $m,n\ge t$ and $m\equiv n\pmod k$.
--
--   They compare letter counts up to a threshold, and distances between positions up to a threshold and modulo $k$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A, p.16

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Threshold congruence `≡_t`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A, p.16): "For each t ∈ ℕ let ≡_t denote the threshold
congruence on ℕ defined as m ≡_t n if m = n or m, n ≥ t." -/
def thrEq (t m n : ℕ) : Prop := m = n ∨ (t ≤ m ∧ t ≤ n)

/-- **`≡^t_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A, p.16): "We define m ≡^t_k n if m = n, or m, n ≥ t and m ≡_k n." -/
def thrModEq (t k m n : ℕ) : Prop := m = n ∨ (t ≤ m ∧ t ≤ n ∧ m % k = n % k)

end CircTrichotomy


