-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
-- name    : MultiCorrectPAC_Demo_Hypotheses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:44:13.20542+00:00
-- url     : https://prove2.me/theorems/253b0a1b-3156-47c9-854e-24be6f32faee
-- title:
--   Multi-label partial hypotheses, projections $\mathcal H|_S$, the intersection class $\mathcal I_R(\mathcal H)$, nondegeneracy, local compatibility, the collapsed class
-- statement:
--   Let $\mathcal X$ (inputs) and $\mathcal Y$ (labels) be sets and $\ell\ge1$ an integer, and put $\mathcal A=\{A\subseteq\mathcal Y:1\le|A|\le\ell\}$. A **multi-label hypothesis** is a map $h:\mathcal X\to\mathcal A\cup\{\star\}$; $h$ is undefined at $x$ if $h(x)=\star$, its **support** is $\operatorname{supp}(h)=\{x:h(x)\ne\star\}$, and $h$ is **total** if $\operatorname{supp}(h)=\mathcal X$. A label $y$ is **correct** for $h$ at $x$ if $x\in\operatorname{supp}(h)$ and $y\in h(x)$. A **class** is a set $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$.
--
--   For a sequence $S=(x_1,\dots,x_n)$ the **projection** is
--   $$\mathcal H|_S=\{(h(x_1),\dots,h(x_n)):h\in\mathcal H,\ \{x_1,\dots,x_n\}\subseteq\operatorname{supp}(h)\}\subseteq\mathcal A^n .$$
--   For an integer $R\ge1$ the **partial intersection class** $\mathcal I_R(\mathcal H)$ consists of all $g$ with $g(x)=\bigcap_{a=1}^r h_a(x)$ for $x\in B$ and $g(x)=\star$ for $x\notin B$, where $1\le r\le R$, $h_1,\dots,h_r\in\mathcal H$ and $B\subseteq\bigcap_a\operatorname{supp}(h_a)$ is any set on which $\bigcap_a h_a(x)\neq\emptyset$.
--
--   $\mathcal H$ is **nondegenerate** if it contains two total hypotheses $x\mapsto\{b_0(x)\}$ and $x\mapsto\{b_1(x)\}$ with $b_0(x)\ne b_1(x)$ for all $x$; it is **locally compatible** if $|h(x)|=1$ and $|h'(x)|\ge2$ for $h,h'\in\mathcal H$ imply $h(x)\subsetneq h'(x)$. For a new label $\diamond\notin\mathcal Y$, the **collapsed hypothesis** is $\tilde h(x)=a$ if $h(x)=\{a\}$, $\tilde h(x)=\diamond$ if $h(x)\ne\star$ and $|h(x)|\ge2$, and $\tilde h(x)=\star$ if $h(x)=\star$; the collapsed class $\tilde{\mathcal H}=\{\tilde h:h\in\mathcal H\}$ is a class with $\ell=1$ over $\mathcal Y\cup\{\diamond\}$.
--
--   **Formalization Note** `Hyp X Y = X → Option (Finset Y)` with `none` for $\star$; `IsClass ℓ H` says every defined value is a nonempty finset of at most $\ell$ labels. Sequences are `S : Fin n → X`. In `interClass R H` the set $B$ is `supp g`; requiring the intersection to be nonempty forces every $h_a$ to be defined there. In `collapse`, $\mathcal Y\cup\{\diamond\}$ is `Option Y` with $\diamond$ = `none`, and the label $a$ is the singleton `{some a}`.
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 25–28 (PDF 27–30), §5.1, (1), (6), (7); pp. 82–83 (PDF 84–85), Definitions 62, 63, (84)

import Mathlib

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
§5.1 (printed pp. 25–26, PDF 27–28), (6)–(7) (pp. 27–28, PDF 29–30), §14.1 Definitions 62, 63
and (84) (pp. 82–83, PDF 84–85).

A multi-label hypothesis `h : X → A ∪ {⋆}` is a function `X → Option (Finset Y)`: the value
`none` is the symbol `⋆` ("undefined"), and `some A` is the correct-label set `A`. -/

/-- A multi-label (partial) hypothesis: `none` encodes `⋆`, `some A` the correct-label set `A`. -/
abbrev Hyp (X Y : Type*) := X → Option (Finset Y)

/-- `y` is a correct label of `h` at `x`: `x ∈ supp(h)` and `y ∈ h(x)`. -/
def IsCorrect {X Y : Type*} (h : Hyp X Y) (x : X) (y : Y) : Prop :=
  ∃ A, h x = some A ∧ y ∈ A

/-- The support `supp(h) = {x : h(x) ≠ ⋆}`. -/
def supp {X Y : Type*} (h : Hyp X Y) : Set X := {x | h x ≠ none}

/-- `h` is total: `supp(h) = X`. -/
def IsTotal {X Y : Type*} (h : Hyp X Y) : Prop := ∀ x, h x ≠ none

/-- `A ∈ 𝒜 = {A ⊆ Y : 1 ≤ |A| ≤ ℓ}` (1). -/
def InA {Y : Type*} (ℓ : ℕ) (A : Finset Y) : Prop := A.Nonempty ∧ A.card ≤ ℓ

/-- `H ⊆ (𝒜 ∪ {⋆})^X`: every defined value of every member is a nonempty set of at most `ℓ`
labels. -/
def IsClass {X Y : Type*} (ℓ : ℕ) (H : Set (Hyp X Y)) : Prop :=
  ∀ h ∈ H, ∀ x A, h x = some A → InA ℓ A

/-- The projection `H|S` of (6), for a sequence `S = (x₁, …, xₙ)` (indices `Fin n`): the patterns
`(h(x₁), …, h(xₙ))` of the members `h ∈ H` defined at every `xᵢ`. -/
def patterns {X Y : Type*} (H : Set (Hyp X Y)) {n : ℕ} (S : Fin n → X) :
    Set (Fin n → Finset Y) :=
  {v | ∃ h ∈ H, ∀ i, h (S i) = some (v i)}

/-- The partial intersection class `I_R(H)` of (7): all `g` for which there are `1 ≤ r ≤ R` and
`h₁, …, h_r ∈ H` such that at every `x` either `g(x) = ⋆`, or `g(x) = ⋂ₐ hₐ(x)` is nonempty
(which forces every `hₐ` to be defined at `x`). The set `B` of (7) is `supp(g)`, an arbitrary set
on which the intersection is nonempty. -/
def interClass {X Y : Type*} (R : ℕ) (H : Set (Hyp X Y)) : Set (Hyp X Y) :=
  {g | ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ ∃ hs : Fin r → Hyp X Y, (∀ a, hs a ∈ H) ∧
    ∀ x, g x = none ∨ ∃ A : Finset Y, g x = some A ∧ A.Nonempty ∧
      ∀ y, y ∈ A ↔ ∀ a, IsCorrect (hs a) x y}

/-- Nondegenerate class (Definition 62): `H` contains two total singleton-valued hypotheses
`x ↦ {b₀(x)}` and `x ↦ {b₁(x)}` with `b₀(x) ≠ b₁(x)` for every `x`. -/
def Nondegenerate {X Y : Type*} (H : Set (Hyp X Y)) : Prop :=
  ∃ b₀ b₁ : X → Y, (fun x => some {b₀ x}) ∈ H ∧ (fun x => some {b₁ x}) ∈ H ∧
    ∀ x, b₀ x ≠ b₁ x

/-- Local compatibility (Definition 63): if `|h(x)| = 1` and `|h'(x)| ≥ 2` then `h(x) ⊂ h'(x)`. -/
def LocallyCompatible {X Y : Type*} (H : Set (Hyp X Y)) : Prop :=
  ∀ h ∈ H, ∀ h' ∈ H, ∀ x (A A' : Finset Y), h x = some A → h' x = some A' →
    A.card = 1 → 2 ≤ A'.card → A ⊂ A'

open Classical in
/-- The collapsed hypothesis `h̃` of (84), over the label space `Y ∪ {⋄}` encoded as `Option Y`
with `⋄ = none`, read as a class with `ℓ = 1` (every defined value a singleton):
`h̃(x) = {a}` if `h(x) = {a}`, `{⋄}` if `h(x) ≠ ⋆` and `|h(x)| ≥ 2`, and `⋆` if `h(x) = ⋆`. -/
noncomputable def collapse {X Y : Type*} (h : Hyp X Y) : Hyp X (Option Y) := fun x =>
  match h x with
  | none => none
  | some A => if hA : ∃ a, A = {a} then some {some hA.choose} else some {none}

/-- The collapsed class `H̃ = {h̃ : h ∈ H}` of (84). -/
def collapsedClass {X Y : Type*} (H : Set (Hyp X Y)) : Set (Hyp X (Option Y)) :=
  collapse '' H

end MultiCorrectPAC.Demo


