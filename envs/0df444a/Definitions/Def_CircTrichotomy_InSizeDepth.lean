-- Prove2me | Definitions.Def_CircTrichotomy_InSizeDepth
-- name    : CircTrichotomy_InSizeDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:41.503662+00:00
-- url     : https://prove2.me/theorems/3f668d79-ab4b-42aa-919c-348ad8edae42
-- title:
--   $L\in\mathrm{SizeDepth}(\mathcal F,\mathcal G)$ and $L\in\mathrm{Size}(\mathcal F)$
-- statement:
--   For classes $\mathcal F,\mathcal G$ of functions,
--   $$\mathrm{SizeDepth}(\mathcal F,\mathcal G)=\{L\subseteq\Sigma^+ \mid \exists\text{ a family } C:\ L(C)=L,\ |C|\in\mathcal F,\ \mathrm{depth}(C)\in\mathcal G\},$$
--   $$\mathrm{Size}(\mathcal F)=\{L\subseteq\Sigma^+ \mid \exists\text{ a family } C:\ L(C)=L,\ |C|\in\mathcal F\}.$$
--   Here $L(C)=L$ means that each $C_n$ (a single-output $n$-circuit) accepts exactly the words of length $n$ in $L$, and $L$ does not contain the empty word.
--
--   **Formalization Note** A class of functions is a predicate on $\mathbb N\to\mathbb R$, e.g. $f\mapsto f\in O(g)$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (20)–(21), p.19

import Mathlib
import Definitions.Def_CircTrichotomy_Circuit

set_option autoImplicit false

namespace CircTrichotomy

/-- **`L ∈ SizeDepth(F, G)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular
Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (21), p.19):
"SizeDepth(F, G) = {L ⊆ Σ⁺ | ∃fam. C : L(C) = L, |C| ∈ F, depth(C) ∈ G}."

`L ⊆ α⁺` (the empty word is not in `L`) and some circuit family `(Cₙ)_{n ∈ ℕ>0}` of single-output
`n`-circuits computes `L` (each `Cₙ` accepts exactly the words of length `n` in `L`), with size
function `n ↦ |Cₙ|` in the class `F` and depth function `n ↦ depth(Cₙ)` in the class `G`.

**Formalization Note** A class of functions is a predicate on `ℕ → ℝ` (e.g. `fun f => BigO f g`
for `O(g)`). The family is `C n hn` for `n > 0`; its size and depth functions are `famSize C` and
`famDepth C` (value `0` at `n = 0`). -/
def InSizeDepth {α : Type} (L : Language α) (F G : (ℕ → ℝ) → Prop) : Prop :=
  [] ∉ L ∧ ∃ C : ∀ n : ℕ, 0 < n → Circuit α n 1,
    (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → α), (C n hn).Accepts w ↔ List.ofFn w ∈ L) ∧
    F (famSize C) ∧ G (famDepth C)

/-- **`L ∈ Size(F)`** ((20), p.19): "Size(F) = {L ⊆ Σ⁺ | ∃fam. C : L(C) = L, |C| ∈ F}." -/
def InSize {α : Type} (L : Language α) (F : (ℕ → ℝ) → Prop) : Prop :=
  [] ∉ L ∧ ∃ C : ∀ n : ℕ, 0 < n → Circuit α n 1,
    (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → α), (C n hn).Accepts w ↔ List.ofFn w ∈ L) ∧
    F (famSize C)

end CircTrichotomy


