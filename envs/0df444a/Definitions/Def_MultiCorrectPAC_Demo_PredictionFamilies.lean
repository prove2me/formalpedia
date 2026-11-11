-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_PredictionFamilies
-- name    : MultiCorrectPAC_Demo_PredictionFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:44:48.775803+00:00
-- url     : https://prove2.me/theorems/d081dc99-2a7c-4f09-9958-f1c0f44750a2
-- title:
--   Prediction families $\mathcal F_{h,S}$ with size bound $B_N$ and the intersection property (Definition 38)
-- statement:
--   Fix $N\ge2$. For a multiset $S=(x_1,\dots,x_N)$ of inputs write $\operatorname{supp}(S)$ for its set of distinct elements; $h$ is **defined on** $S$ if $\operatorname{supp}(S)\subseteq\operatorname{supp}(h)$. Suppose that for every multiset $S$ of $N$ inputs and every $h\in\mathcal H$ defined on $S$ a family $\mathcal F_{h,S}\subseteq\{f:\operatorname{supp}(S)\to\mathcal Y\}$ with $|\mathcal F_{h,S}|\le B_N$ is given, $B_N\ge1$ independent of $S$ and $h$. The families have the **intersection property** if for every such $S$ and all $h_1,\dots,h_{\ell+1}\in\mathcal H$ defined on $S$ there is $f\in\bigcap_{a=1}^{\ell+1}\mathcal F_{h_a,S}$ with
--   $$\bigcap_{a=1}^{\ell+1}h_a(x)\ne\emptyset\implies f(x)\in\bigcap_{a=1}^{\ell+1}h_a(x)\qquad(x\in\operatorname{supp}(S)).\tag{44}$$
--
--   **Formalization Note** Multisets are `Multiset X` with `card = N`; $\operatorname{supp}(S)$ is the subtype `{x // x ∈ S}`; the families are a single function `F : (S : Multiset X) → Hyp X Y → Finset ({x // x ∈ S} → Y)`, of which only the values at `card S = N` and `h ∈ H` defined on `S` are constrained. `HasIntersectionProperty ℓ N B H F` bundles $B\ge1$, the size bound and (44).
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 55–56 (PDF 57–58), Definition 38, (44)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
Definition 38 (printed pp. 55–56, PDF 57–58). A multiset `S` of `N` inputs is a
`Multiset X` with `card = N`; `supp(S)` is the subtype `{x // x ∈ S}` of its distinct
elements. A family of single-label predictions on `supp(S)` is a `Finset` of functions
`{x // x ∈ S} → Y`; families are given for every multiset and hypothesis, and only those for
`|S| = N` and `h ∈ H` defined on `S` are constrained. -/

/-- `h` is defined on the multiset `S`: `supp(S) ⊆ supp(h)`. -/
def DefinedOn {X Y : Type*} (h : Hyp X Y) (S : Multiset X) : Prop :=
  ∀ x ∈ S, h x ≠ none

/-- Families `F_{h,S}` with size bound `B_N ≥ 1` and the intersection property (44) of
Definition 38, for `N`, the bound `ℓ` on correct labels and the class `H`. -/
def HasIntersectionProperty {X Y : Type*} (ℓ N B : ℕ) (H : Set (Hyp X Y))
    (F : (S : Multiset X) → Hyp X Y → Finset ({x // x ∈ S} → Y)) : Prop :=
  1 ≤ B ∧
  (∀ (S : Multiset X), S.card = N → ∀ h ∈ H, DefinedOn h S → (F S h).card ≤ B) ∧
  ∀ (S : Multiset X), S.card = N → ∀ hs : Fin (ℓ + 1) → Hyp X Y,
    (∀ a, hs a ∈ H) → (∀ a, DefinedOn (hs a) S) →
    ∃ f : {x // x ∈ S} → Y, (∀ a, f ∈ F S (hs a)) ∧
      ∀ x : {x // x ∈ S}, (∃ y, ∀ a, IsCorrect (hs a) x.1 y) → ∀ a, IsCorrect (hs a) x.1 (f x)

end MultiCorrectPAC.Demo


