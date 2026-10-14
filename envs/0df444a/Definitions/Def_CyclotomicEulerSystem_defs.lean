-- Prove2me | Definitions.Def_CyclotomicEulerSystem_defs
-- name    : CyclotomicEulerSystem_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T15:26:33.29234+00:00
-- url     : https://prove2.me/theorems/9f3a8512-2b39-4a7a-a04f-b329f8b26173
-- title:
--   Cyclotomic Euler system: compatible roots of unity, cyclotomic fields and units
-- statement:
--   This file fixes the objects of the cyclotomic Euler system.
--
--   1. A function $\zeta:\mathbb N\to\mathbb C$, $n\mapsto\zeta_n$, is a **compatible system of roots of unity** if for every square-free positive integer $n$ the number $\zeta_n$ is a primitive $n$-th root of unity, and
--   $$\zeta_{mn}=\zeta_m\,\zeta_n\qquad\text{whenever } m,n \text{ are coprime square-free positive integers.}$$
--   2. For $n\in\mathbb N$, $\mathbb Q(\zeta_n)$ denotes the subfield of $\mathbb C$ generated over $\mathbb Q$ by $\zeta_n$ (the $n$-th cyclotomic field when $n$ is square-free).
--   3. The **cyclotomic units** are the numbers $\alpha_n = 1-\zeta_n$; they are also packaged as elements of $\mathbb Q(\zeta_n)$.
--   4. For $n,m$, the field $\mathbb Q(\zeta_n)(\zeta_m)\subseteq\mathbb C$ is regarded as an extension of $\mathbb Q(\zeta_n)$, and $\alpha_m$ as an element of it. For $m=nl$ this is the field $\mathbb Q(\zeta_{nl})$ viewed over $\mathbb Q(\zeta_n)$, which is the extension appearing in the norm relation.
--
--   These are the shared definitions for every statement of the mission.
--
--   **Formalization Note** The values of $\zeta$ at non-square-free arguments are unconstrained and never used. In Lean, `Squarefree n` for natural numbers already excludes $n=0$. The source says "an $n$-th root of 1"; the standard construction (and the validity of the relations) requires *primitive* roots, which is what is encoded. The file contains only definitions and the membership facts needed to form the elements.
-- source:
--   Wikipedia, "Euler system", revision 1353502478 (https://en.wikipedia.org/w/index.php?title=Euler_system&oldid=1353502478), section "Examples / Cyclotomic units", displayed relations (norm relation and congruence relation) and the preceding sentence "For every square-free positive integer n pick an n-th root ζ_n of 1, with ζ_mn = ζ_m ζ_n for m,n coprime. Then the cyclotomic Euler system is the set of numbers α_n = 1 − ζ_n."

import Mathlib

/-!
# Cyclotomic Euler system — definitions

Draft definition layer for the Prove2Me mission proposal
"Euler systems: the cyclotomic Euler system" (source: Wikipedia, *Euler system*,
section *Examples / Cyclotomic units*).
-/

namespace CyclotomicEulerSystem

/-- A *compatible system of roots of unity*: for every square-free positive integer `n`,
`ζ n` is a primitive `n`-th root of unity in `ℂ`, and `ζ (m * n) = ζ m * ζ n` whenever
`m`, `n` are coprime square-free positive integers. (In `ℕ`, `Squarefree n` already
forces `n ≠ 0`.) -/
def IsCompatibleRootSystem (ζ : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, Squarefree n → IsPrimitiveRoot (ζ n) n) ∧
    ∀ m n : ℕ, Squarefree m → Squarefree n → Nat.Coprime m n → ζ (m * n) = ζ m * ζ n

/-- The cyclotomic field `ℚ(ζₙ)`, as a subfield of `ℂ`. -/
noncomputable def cycField (ζ : ℕ → ℂ) (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {ζ n}

/-- The cyclotomic unit `αₙ = 1 - ζₙ`, as a complex number. -/
def alpha (ζ : ℕ → ℂ) (n : ℕ) : ℂ := 1 - ζ n

theorem zeta_mem_cycField (ζ : ℕ → ℂ) (n : ℕ) : ζ n ∈ cycField ζ n :=
  IntermediateField.subset_adjoin ℚ {ζ n} rfl

theorem alpha_mem_cycField (ζ : ℕ → ℂ) (n : ℕ) : alpha ζ n ∈ cycField ζ n :=
  sub_mem (one_mem _) (zeta_mem_cycField ζ n)

/-- `ζₙ` as an element of `ℚ(ζₙ)`. -/
noncomputable def zetaIn (ζ : ℕ → ℂ) (n : ℕ) : cycField ζ n :=
  ⟨ζ n, zeta_mem_cycField ζ n⟩

/-- `αₙ = 1 - ζₙ` as an element of `ℚ(ζₙ)`. -/
noncomputable def alphaIn (ζ : ℕ → ℂ) (n : ℕ) : cycField ζ n :=
  ⟨alpha ζ n, alpha_mem_cycField ζ n⟩

/-- The field `ℚ(ζₙ)(ζₘ)`, viewed as an extension of `ℚ(ζₙ)` inside `ℂ`.
For `m = n * l` this is `ℚ(ζₙₗ)` regarded as an extension of `ℚ(ζₙ)`. -/
noncomputable def cycExt (ζ : ℕ → ℂ) (n m : ℕ) : IntermediateField (cycField ζ n) ℂ :=
  IntermediateField.adjoin (cycField ζ n) {ζ m}

theorem alpha_mem_cycExt (ζ : ℕ → ℂ) (n m : ℕ) : alpha ζ m ∈ cycExt ζ n m :=
  sub_mem (one_mem _) (IntermediateField.subset_adjoin (cycField ζ n) {ζ m} rfl)

/-- `αₘ = 1 - ζₘ` as an element of the extension `ℚ(ζₙ)(ζₘ)` of `ℚ(ζₙ)`. -/
noncomputable def alphaExt (ζ : ℕ → ℂ) (n m : ℕ) : cycExt ζ n m :=
  ⟨alpha ζ m, alpha_mem_cycExt ζ n m⟩

end CyclotomicEulerSystem


