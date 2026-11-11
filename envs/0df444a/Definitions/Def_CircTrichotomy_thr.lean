-- Prove2me | Definitions.Def_CircTrichotomy_thr
-- name    : CircTrichotomy_thr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:07.752579+00:00
-- url     : https://prove2.me/theorems/606b5dea-29a4-4daa-8459-110790b69a98
-- title:
--   Modular threshold languages $\mathrm{Thr}_{i,k}(a,t)$
-- statement:
--   For $k,t\ge1$, $i\in[0,k-1]$ and $a\in\Sigma$,
--   $$\mathrm{Thr}_{i,k}(a,t)=\{w\in\Sigma^+ : |\pi_{i,k}(w)|_a\ge t\},$$
--   the non-empty words with at least $t$ occurrences of $a$ at positions congruent to $i$ modulo $k$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.22, p.33

import Mathlib
import Definitions.Def_CircTrichotomy_piMod

set_option autoImplicit false

namespace CircTrichotomy

/-- **Modular threshold language `Thr_{i,k}(a, t)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.22, p.33): "For each
k, t ∈ ℕ>0, i ∈ [0, k − 1] and a ∈ Σ the language Thr_{i,k}(a, t) is defined to be
Thr_{i,k}(a, t) = {w ∈ Σ⁺ : |π_{i,k}(w)|_a ≥ t}.   (105)" -/
def thr {α : Type} (k i : ℕ) (a : α) (t : ℕ) : Language α :=
  {w | w ≠ [] ∧ t ≤ cntMod k i a w}

end CircTrichotomy


