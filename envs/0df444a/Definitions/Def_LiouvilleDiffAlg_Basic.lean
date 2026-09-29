-- Prove2me | Definitions.Def_LiouvilleDiffAlg_Basic
-- name    : LiouvilleDiffAlg_Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T17:18:07.537634+00:00
-- url     : https://prove2.me/theorems/216ed798-f8af-4a7c-abf7-2ee35e476a83
-- title:
--   Constants, logarithmic/exponential extensions, elementary differential extensions
-- statement:
--   Basic notions of differential algebra, following the section "Definitions" of the source.
--
--   Let $F$ be a differential field with derivation $D$.
--
--   1. The **constants** of $F$ are $\operatorname{Con}(F) = \{ f \in F : Df = 0 \}$ (`constants F`).
--   2. Let $G$ be a differential field extension of $F$ and $K$ an intermediate field. An element $t \in G$ is a **logarithmic generator** over $K$ if $t$ is transcendental over $K$ and $Dt = Ds/s$ for some nonzero $s \in K$. It is an **exponential generator** over $K$ if $t$ is transcendental over $K$ and $Dt/t = Ds$ for some $s \in K$.
--   3. $G$ is a **logarithmic extension** of $F$ if $G = F(t)$ with $t$ transcendental over $F$ and $Dt = Ds/s$ for some nonzero $s\in F$. It is an **exponential extension** if $G = F(t)$ with $t$ transcendental over $F$ and $Dt/t = Ds$ for some $s \in F$.
--   4. $G$ is an **elementary differential extension** of $F$ if there is a finite chain
--   $$F = K_0 \subseteq K_1 \subseteq \cdots \subseteq K_m = G$$
--   of intermediate fields with $K_{i+1} = K_i(t_i)$, where each $t_i$ is algebraic over $K_i$, a logarithmic generator over $K_i$, or an exponential generator over $K_i$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** A differential field is a `Field` with a `Differential` instance. The extension is an `Algebra F G` with `DifferentialAlgebra F G`. Intermediate fields are `IntermediateField F G`, and $K_i(t_i)$ is `IntermediateField.adjoin F (insert t (K i))`. All derivatives in the chain are taken in $G$.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Definitions"

import Mathlib

namespace LiouvilleDiffAlg

open scoped Differential

/-- The constants of a differential field `F`: `Con(F) = {f ∈ F : Df = 0}`. -/
def constants (F : Type*) [Field F] [Differential F] : Set F :=
  {f | f′ = 0}

section Steps

variable {F G : Type*} [Field F] [Field G] [Differential G] [Algebra F G]

/-- `t ∈ G` is a *logarithmic generator* over the intermediate field `K` of `G / F`:
`t` is transcendental over `K` and `Dt = Ds / s` for some nonzero `s ∈ K`. -/
def IsLogarithmicOver (K : IntermediateField F G) (t : G) : Prop :=
  Transcendental K t ∧ ∃ s ∈ K, s ≠ 0 ∧ t′ = s′ / s

/-- `t ∈ G` is an *exponential generator* over the intermediate field `K` of `G / F`:
`t` is transcendental over `K` and `Dt / t = Ds` for some `s ∈ K`. -/
def IsExponentialOver (K : IntermediateField F G) (t : G) : Prop :=
  Transcendental K t ∧ ∃ s ∈ K, t′ / t = s′

end Steps

section Extensions

variable (F G : Type*) [Field F] [Field G] [Differential F] [Differential G]
  [Algebra F G] [DifferentialAlgebra F G]

/-- `G` is a *logarithmic extension* of `F`: `G = F(t)` for some `t` transcendental over `F`
with `Dt = Ds / s` for some nonzero `s ∈ F`. -/
def IsLogarithmicExtension : Prop :=
  ∃ t : G, IntermediateField.adjoin F {t} = ⊤ ∧ Transcendental F t ∧
    ∃ s : F, s ≠ 0 ∧ t′ = (algebraMap F G s)′ / algebraMap F G s

/-- `G` is an *exponential extension* of `F`: `G = F(t)` for some `t` transcendental over `F`
with `Dt / t = Ds` for some `s ∈ F`. -/
def IsExponentialExtension : Prop :=
  ∃ t : G, IntermediateField.adjoin F {t} = ⊤ ∧ Transcendental F t ∧
    ∃ s : F, t′ / t = (algebraMap F G s)′

/-- `G` is an *elementary differential extension* of `F`: there is a finite chain of
intermediate fields `F = K₀ ⊆ K₁ ⊆ ⋯ ⊆ Kₘ = G` such that each `Kᵢ₊₁ = Kᵢ(tᵢ)` is obtained
from `Kᵢ` by adjoining a single element `tᵢ` which is algebraic over `Kᵢ`, or a logarithmic
generator over `Kᵢ`, or an exponential generator over `Kᵢ`. -/
def IsElementaryDifferentialExtension : Prop :=
  ∃ (m : ℕ) (K : ℕ → IntermediateField F G), K 0 = ⊥ ∧ K m = ⊤ ∧
    ∀ i < m, ∃ t : G, K (i + 1) = IntermediateField.adjoin F (insert t (K i : Set G)) ∧
      (IsAlgebraic (K i) t ∨ IsLogarithmicOver (K i) t ∨ IsExponentialOver (K i) t)

end Extensions

end LiouvilleDiffAlg


