-- Prove2me | Definitions.Def_AlgSemNondet_Main_AlgebraicEncoding
-- name    : AlgSemNondet_Main_AlgebraicEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:46:07.978207+00:00
-- url     : https://prove2.me/theorems/d919845c-afc0-446f-8852-9c7bd6dbf369
-- title:
--   Definition 4.4 — algebraic encoding and encoded incommensurability
-- statement:
--   An **algebraic encoding** assigns to each data (non-blank) symbol $c \in \Gamma \setminus \{B\}$ an algebraic number $\varepsilon_0(c)$; algebraic numbers are modelled as complex numbers algebraic over $\mathbb Q$. For a word $w$, $\varepsilon(w) = \{\varepsilon_0(c) : c \text{ is a non-blank symbol occurring in } w\}$ is the *set* (not multiset) of values. On input $w$, the machine **associates $\varepsilon$-incommensurable elements** if $\varepsilon(w)$ contains two elements $\gamma, \delta$ that are incommensurable over $\mathbb Q$: both nonzero and linearly independent over $\mathbb Q$.
--
--   Formalization Note: the predicate takes no machine argument, because Definition 4.4 makes it depend only on $w$ and $\varepsilon$. The set $\mathbb A \subseteq \overline{\mathbb Q}$ of Definition 4.4 is taken to be all of $\overline{\mathbb Q}$, realized inside $\mathbb C$.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Definition 4.4, p.17, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_Incommensurable

namespace AlgSemNondet.Main

/-- Definition 4.4 (algebraic encoding): `ε₀ : Γ \ {B} → 𝔸` assigns to each data symbol an
algebraic number; `𝔸 ⊆ ℚ̄` is modelled as the complex numbers algebraic over `ℚ`. -/
structure AlgebraicEncoding (Γ : Type*) (B : Γ) where
  /-- The value of each data (non-blank) symbol. -/
  ε₀ : {c : Γ // c ≠ B} → ℂ
  /-- Every value is an algebraic number. -/
  isAlgebraic : ∀ c, IsAlgebraic ℚ (ε₀ c)

namespace AlgebraicEncoding

variable {Γ : Type*} {B : Γ}

/-- `ε(w) = {ε₀(c) : c is a symbol occurring in w}`, the *set* (not multiset) of values of the
data symbols occurring in `w`. -/
def image (ε : AlgebraicEncoding Γ B) (w : List Γ) : Set ℂ :=
  {z | ∃ (c : Γ) (hc : c ≠ B), c ∈ w ∧ ε.ε₀ ⟨c, hc⟩ = z}

/-- Definition 4.4: on input `w`, the machine *associates `ε`-incommensurable elements* iff
`ε(w)` contains two nonzero elements `γ, δ` that are linearly independent over `ℚ`
(Definition 3.11). The predicate depends only on `ε` and `w`, not on the machine. -/
def AssociatesIncommensurable (ε : AlgebraicEncoding Γ B) (w : List Γ) : Prop :=
  ∃ γ ∈ ε.image w, ∃ δ ∈ ε.image w, Incommensurable ℚ γ δ

end AlgebraicEncoding

end AlgSemNondet.Main


