-- Prove2me | Definitions.Def_RhoArbitrage_IsRieszL
-- name    : RhoArbitrage_IsRieszL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:46.103348+00:00
-- url     : https://prove2.me/theorems/e76699c9-2b46-4c15-bdad-0c3e8fea8b4a
-- title:
--   The Riesz space $L^\infty\subset L\subset L^1$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. Risk is measured on a **Riesz space** $L$ with
--
--   $$
--   L^\infty\subset L\subset L^1 .
--   $$
--
--   That is, $L$ is a linear space of real random variables, closed under $X\mapsto|X|$ (hence under $\max$ and $\min$), each of its members is $\mathbb P$-integrable, and each essentially bounded random variable belongs to it. Examples are the spaces $L^p$ for $p\in[1,\infty]$, Orlicz hearts and Orlicz spaces.
--
--   This is the space of financial positions on which every risk functional of the mission lives. No solidity or closedness is required.
--
--   **Formalization Note** The paper's elements are $\mathbb P$-a.s. classes. Lean takes $L$ as the set of all representatives, a set of functions $\Omega\to\mathbb R$. The conditions force closure under $\mathbb P$-a.s. equality.
-- source:
--   Herdegen, Khan, ρ-arbitrage and ρ-consistent pricing for star-shaped risk measures, arXiv:2202.07610v3, §2.1, p.4

import Mathlib

open MeasureTheory

namespace RhoArbitrage

/-- **The Riesz space `L∞ ⊂ L ⊂ L¹`.** Herdegen–Khan, arXiv:2202.07610v3, §2.1, p.4: "We fix a
probability space `(Ω, F, P)` and work on a Riesz space `L∞ ⊂ L ⊂ L¹`."

`IsRieszL P L` says that the set `L` of real functions on `Ω` is a linear subspace of `Ω → ℝ`
closed under `|·|` (hence under `max` and `min`, so a Riesz subspace), that every member of `L`
is `P`-integrable (`L ⊂ L¹`), and that every a.e.-strongly-measurable, `P`-a.s. bounded function
is in `L` (`L∞ ⊂ L`).

**Formalization Note.** The paper's `L` consists of `P`-a.s. equivalence classes; here `L` is the
set of all their representatives. The conditions imply that `L` is closed under `P`-a.s. equality:
if `X ∈ L` and `Y =ᵐ[P] X`, then `Y - X` is a.s. bounded and a.e.-strongly-measurable, so
`Y = X + (Y - X) ∈ L`. `L` is **not** required to be solid (an ideal) or closed: the paper says
Riesz space. -/
structure IsRieszL {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Set (Ω → ℝ)) : Prop where
  /-- `L` contains `0`. -/
  zero_mem : (0 : Ω → ℝ) ∈ L
  /-- `L` is closed under addition. -/
  add_mem : ∀ X ∈ L, ∀ Y ∈ L, X + Y ∈ L
  /-- `L` is closed under scalar multiplication. -/
  smul_mem : ∀ (c : ℝ), ∀ X ∈ L, c • X ∈ L
  /-- `L` is closed under the absolute value (the Riesz structure). -/
  abs_mem : ∀ X ∈ L, (fun ω => |X ω|) ∈ L
  /-- `L ⊂ L¹`. -/
  integrable : ∀ X ∈ L, Integrable X P
  /-- `L∞ ⊂ L`. -/
  bounded_mem : ∀ X : Ω → ℝ, AEStronglyMeasurable X P → (∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C) → X ∈ L

end RhoArbitrage


