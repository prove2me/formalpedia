-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15
-- name    : NestedLogitAssort_DeltaGrid_IsApprox15
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:07:01.818562+00:00
-- url     : https://prove2.me/theorems/d1a3c9d7-338c-49d6-a252-51e7641404b8
-- title:
--   $\delta$-approximate solution $\hat S_{il}$ of problem (15)
-- statement:
--   Fix $\delta>1$, a nest $i$ and a level $l$. An assortment $\hat S$ has the two properties that define $\hat S_{il}$ when
--
--   1. $\hat S$ is feasible for (15): $\delta^{l-1}\le v_{i0}+\sum_{j\in\hat S}v_{ij}\le\delta^l$;
--   2. its objective value is within a factor $\delta$ of the optimum: $\delta\sum_{j\in\hat S}r_{ij}v_{ij}\ge\hat G_{il}$, where $\hat G_{il}$ is the optimal value of (15).
--
--   The paper obtains such an assortment from Proposition 15, and the candidate collection of Theorem 12 is built from these assortments.
--
--   **Formalization Note** Since $\hat S$ itself lies in the window, $\hat G_{il}$ is the maximum of a finite nonempty set, and property 2 is stated equivalently as $\delta\sum_{j\in\hat S}r_{ij}v_{ij}\ge\sum_{j\in S}r_{ij}v_{ij}$ for every assortment $S$ in the window. No real supremum is used.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.2, p. 28

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Window

namespace NestedLogitAssort.DeltaGrid

/-- **`Ŝ` is a `δ`-approximate solution of problem (15): the defining properties of `Ŝ_{il}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.2, p. 28: "we can find an assortment `Ŝ_{il}` that satisfies
`δ^{l−1} ≤ v_{i0} + ∑_{j∈Ŝ_{il}} v_{ij} ≤ δ^l` and `δ ∑_{j∈Ŝ_{il}} r_{ij} v_{ij} ≥ Ĝ_{il}`", where
`Ĝ_{il} = max_{S_i ⊂ N} {∑_{j∈S_i} r_{ij} v_{ij} : δ^{l−1} ≤ v_{i0} + ∑_{j∈S_i} v_{ij} ≤ δ^l}` (15).

**Formalization Note.** `Ĝ_{il}` is the maximum of a finite set that is nonempty because `Ŝ`
itself lies in the window. So `δ ∑_{Ŝ} r v ≥ Ĝ_{il}` is stated, equivalently, as
`δ ∑_{Ŝ} r v ≥ ∑_{S} r v` for every assortment `S` in the window, which avoids a real
supremum. -/
def IsApprox15 {M : Type*} {n : ℕ} (I : Instance M n) (δ : ℝ) (i : M) (l : ℤ)
    (Shat : Finset (Fin n)) : Prop :=
  Window I δ i l Shat ∧
    ∀ S : Finset (Fin n), Window I δ i l S →
      ∑ j ∈ S, I.r i j * I.v i j ≤ δ * ∑ j ∈ Shat, I.r i j * I.v i j

end NestedLogitAssort.DeltaGrid


