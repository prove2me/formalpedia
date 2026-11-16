-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_HasNeutralLetter
-- name    : CircTrichotomy_Supplement_HasNeutralLetter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:13:40.979057+00:00
-- url     : https://prove2.me/theorems/9bdd39a5-bf71-4a36-afca-71f570149325
-- title:
--   Neutral letters and neutral letter languages
-- statement:
--   Let $L\subseteq\Sigma^+$. A letter $c\in\Sigma$ is **neutral** for $L$ if
--   $$uv\in L \iff ucv\in L \qquad\text{for all } u,v\in\Sigma^* \text{ with } uv\neq\varepsilon.$$
--   $L$ is a **neutral letter language** if it has a neutral letter.
--
--   Inserting or deleting a neutral letter never changes membership, so a neutral letter language cannot test positions or lengths; this is the hypothesis of Theorem 5.1.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §5, p.10; §B.5.1, pp.39–40

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- **Neutral letter** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §5, p.10; §B.5.1, p.39): "For
L ⊆ Σ+, a letter c ∈ Σ is neutral if uv ∈ L if and only if ucv ∈ L for all u, v ∈ Σ∗ with
uv ≠ ε." -/
def IsNeutralLetter {α : Type} (L : Language α) (c : α) : Prop :=
  ∀ u v : List α, u ++ v ≠ [] → (u ++ v ∈ L ↔ u ++ [c] ++ v ∈ L)

/-- **Neutral letter language** (§B.5.1, pp.39–40): "A language L ⊆ Σ+ has a neutral letter if
there exists a letter c ∈ Σ such that uv ∈ L if, and only if, ucv ∈ L for all u, v ∈ Σ∗ such that
uv ∈ Σ+. A language having a neutral letter is called a neutral letter language." -/
def HasNeutralLetter {α : Type} (L : Language α) : Prop :=
  ∃ c : α, IsNeutralLetter L c

end Supplement

end CircTrichotomy


