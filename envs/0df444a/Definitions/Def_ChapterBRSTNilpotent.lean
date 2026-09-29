-- Prove2me | Definitions.Def_ChapterBRSTNilpotent
-- name    : ChapterBRSTNilpotent
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:13:43.571586+00:00
-- url     : https://prove2.me/theorems/b9e95361-14d0-4dbf-814d-0f292b269cce
-- title:
--   Nilpotency of the pure-SU(3) BRST charge
-- statement:
--   Formal definitions for the Nilpotency of the pure-SU(3) BRST charge of the timepiece Lean 4 formalization (module `BookProof.BRSTNilpotent`, source chapter `BookProof/ChapterBRSTNilpotent.lean`).
--
--   This file formalizes the central algebraic fact behind the book's BRST/gauge programme (`book.tex` lines ~7050 and ~7343): the **nilpotency of the BRST charge**
--
--   `Ω(x) = π^μ_a ∂_μ ψ†_a − π^μ_a f_{abc} A_{μ b} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c`,
--
--   `Ω² = 0`, which is what makes the BRST cohomology (hence the physical / gauge-invariant algebra that the book proposes as the definition of Quantum Yang-Mills) well defined.
--
--   We isolate the **cubic ghost term**, the only part whose nilpotency requires the non-abelian structure of the gauge group, and prove that it squares to zero. Concretely: in any associative `ℝ`-algebra `R`, given
--
--   * ghost creation operators `χ : Fin n → R` (the book's `ψ†_a`) and annihilation operators `β : Fin n → R` (the book's `ψ_a`) satisfying the **canonical anticommutation relations** `{χ_a, χ_b} = 0`, `{β_a, β_b} = 0`, `{β_a, χ_b} = δ_{ab}`, and * real structure constants `f : Fin n → Fin n → Fin n → ℝ` that are **antisymmetric** in their first two indices and satisfy the **Jacobi identity** `∑_e (f_{abe} f_{ecg} + f_{bce} f_{eag} + f_{cae} f_{ebg}) = 0` (both proved for the SU(N) generators in `ChapterYangMillsSU3.lean`),
--
--   the cubic ghost charge
--
--   `Q = ∑_{a,b,e} f_{abe} · (χ_a χ_b β_e)`
--
--   satisfies `Q · Q = 0` (`brst_charge_nilpotent`).
--
--   The proof normal-orders `Q²`: pushing the middle annihilation operator through the two creation operators (`beta_move`) splits `Q²` into a **purely quartic** ghost term that vanishes by fermionic antisymmetry alone (`quartic_term_zero`, using `chi_swap4`) and two **contracted** terms that combine and vanish by the Jacobi identity (`contracted_terms_zero`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBRSTNilpotent.lean

import Mathlib

/-!
# Chapter *"Quantization due to time-evolution: Yang-Mills and Classical Statistical Field Theory"*,
§*"Pure SU(3) Yang-Mills theory"*: nilpotency of the BRST charge

This file formalizes the central algebraic fact behind the book's BRST/gauge
programme (`book.tex` lines ~7050 and ~7343): the **nilpotency of the BRST
charge**

  `Ω(x) = π^μ_a ∂_μ ψ†_a − π^μ_a f_{abc} A_{μ b} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c`,

`Ω² = 0`, which is what makes the BRST cohomology (hence the physical /
gauge-invariant algebra that the book proposes as the definition of Quantum
Yang-Mills) well defined.

We isolate the **cubic ghost term**, the only part whose nilpotency requires the
non-abelian structure of the gauge group, and prove that it squares to zero.
Concretely: in any associative `ℝ`-algebra `R`, given

* ghost creation operators `χ : Fin n → R` (the book's `ψ†_a`) and annihilation
  operators `β : Fin n → R` (the book's `ψ_a`) satisfying the **canonical
  anticommutation relations**
  `{χ_a, χ_b} = 0`, `{β_a, β_b} = 0`, `{β_a, χ_b} = δ_{ab}`, and
* real structure constants `f : Fin n → Fin n → Fin n → ℝ` that are
  **antisymmetric** in their first two indices and satisfy the **Jacobi
  identity** `∑_e (f_{abe} f_{ecg} + f_{bce} f_{eag} + f_{cae} f_{ebg}) = 0`
  (both proved for the SU(N) generators in `ChapterYangMillsSU3.lean`),

the cubic ghost charge

  `Q = ∑_{a,b,e} f_{abe} · (χ_a χ_b β_e)`

satisfies `Q · Q = 0` (`brst_charge_nilpotent`).

The proof normal-orders `Q²`: pushing the middle annihilation operator through
the two creation operators (`beta_move`) splits `Q²` into a **purely quartic**
ghost term that vanishes by fermionic antisymmetry alone (`quartic_term_zero`,
using `chi_swap4`) and two **contracted** terms that combine and vanish by the
Jacobi identity (`contracted_terms_zero`).
-/

namespace BookProof.BRSTNilpotent

variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

/-- Canonical anticommutation relations for the ghost creation (`χ`, i.e. `ψ†`)
and annihilation (`β`, i.e. `ψ`) operators. -/
structure GhostCAR (χ β : Fin n → R) : Prop where
  /-- creation operators anticommute: `{χ_a, χ_b} = 0`. -/
  chichi : ∀ a b, χ a * χ b + χ b * χ a = 0
  /-- annihilation operators anticommute: `{β_a, β_b} = 0`. -/
  betabeta : ∀ a b, β a * β b + β b * β a = 0
  /-- mixed relation: `{β_a, χ_b} = δ_{ab}·1`. -/
  betachi : ∀ a b, β a * χ b + χ b * β a = if a = b then 1 else 0

/-- The cubic ghost part of the BRST charge,
`Q = ∑_{a,b,e} f_{abe} · (χ_a · χ_b · β_e)`. -/
noncomputable def Q (f : Fin n → Fin n → Fin n → ℝ) (χ β : Fin n → R) : R :=
  ∑ a, ∑ b, ∑ e, f a b e • (χ a * χ b * β e)







/-
**The purely quartic ghost term vanishes.**  The fully normal-ordered piece
of `Q²`, `∑ f_{abe} f_{dgh} · (χ_a χ_b χ_d χ_g β_e β_h)`, is antisymmetric under
exchanging the two `Q`-factors (even sign on the four `χ`'s, odd sign on the two
`β`'s), hence equals its own negative and so is zero.
-/


/-
**The contracted terms vanish by the Jacobi identity.**  The two terms
produced by contracting the middle `β` against the second pair of `χ`'s combine
to `2·∑_{a,b,g,h} (∑_e f_{abe} f_{egh}) · (χ_a χ_b χ_g β_h)`; contracting the
totally-antisymmetric `χ_a χ_b χ_g` against the coefficient antisymmetrizes it,
which is exactly the Jacobi combination and so vanishes.
-/


/-
**Nilpotency of the (cubic) BRST charge, `Q² = 0`.**  Given the ghost
canonical anticommutation relations and structure constants that are
antisymmetric in their first two indices and satisfy the Jacobi identity, the
cubic ghost part of the BRST charge is nilpotent — the property that makes the
BRST cohomology, and hence the book's definition of the gauge-invariant
(physical) algebra of Quantum Yang-Mills, well defined.
-/


end BookProof.BRSTNilpotent


