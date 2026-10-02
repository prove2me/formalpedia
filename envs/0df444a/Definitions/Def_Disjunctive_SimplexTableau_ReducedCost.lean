-- Prove2me | Definitions.Def_Disjunctive_SimplexTableau_ReducedCost
-- name    : Disjunctive_SimplexTableau_ReducedCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:50:51.295465+00:00
-- url     : https://prove2.me/theorems/b52f9abb-b131-4fda-afad-a60d7ba0534e
-- title:
--   σ, the pivoted-out extension, and the CGLP column reduced costs
-- statement:
--   This definition fixes the machinery of Theorem 9.2's proof: the normalizing
--   coefficient `σ`, the explicit extension of a basic `(CGLP)_k` solution obtained by pivoting a row
--   `i` out of the basis with multiplier values `u_i,v_i` (eq. (9.7)-(9.9)), and the resulting reduced
--   costs `r_ui,r_vi` (eq. (9.6)).
--
--   `SigmaCoef` is `σ` (the base solution's objective value, before scaling). `U0PlusV0Ext`/`VExt`/
--   `V0Ext` are `u0+v0`, `v_j` (`j∈M2`), and `v0` at the *extended* solution obtained by setting
--   `u_i,v_i` to given values and re-solving the eliminated system (8.3) for feasibility (eq.
--   (9.8)-(9.9)) — an explicit, independently-computed construction, not the closed form being proved.
--   `ObjExt` is the resulting `(CGLP)_k` objective `αx̄-β`, computed via the identity `α=vÃ+v0e_k,
--   β=vb̃+v0` (from `(8.1)`'s own equations) as `v_{M2}·s̄_{M2} + v_i·s̄_i + v0(x̄_k-1)`.
--   `ReducedCostU`/`ReducedCostV` are the closed-form reduced costs of eq. (9.6).
--
--   **Formalization Note.** `ObjExt` is built independently of `ReducedCostU`/`ReducedCostV` (via the
--   extension construction, not by definition), so that Theorem 9.2's assertion that they coincide —
--   `ObjExt = σ + u_i·r_ui + v_i·r_vi` — is genuine mathematical content, matching the book's own "we
--   can then read the reduced costs `rui` and `rvi` as the coefficients of `ui` and `vi`" in this
--   expansion, not a restatement of a definition.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 109-113, Section 9.1

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau

namespace Disjunctive.SimplexTableau

/-- `σ`, the normalizing coefficient of eq. (9.6)-(9.7) (Balas §9.1, p. 110): the value of
`(CGLP)_k`'s objective at the base solution (`u_i=v_i=0`), before scaling by the sum of
multipliers. `M1, M2` are the row-*positions* (via `ι`) of the basic `u`/`v`-components, matching
`08-cut-correspondence`'s convention adapted to this chapter's own `J ≃ Fin n` enumeration. -/
noncomputable def SigmaCoef {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (xbar : Fin n → ℝ) : ℝ :=
  ((∑ j ∈ M2, Abar Atil ι k j * SurplusM Atil btil (ι j) xbar) -
      Abar0 Atil btil ι k * (1 - xbar k)) /
    (1 + ∑ j ∈ M1 ∪ M2, |Abar Atil ι k j|)

/-- `u0+v0` for the solution extended by pivoting `x_i` out of the basis with multiplier values
`u_i, v_i` (Balas §9.1, eq. (9.9), p. 111-112). -/
noncomputable def U0PlusV0Ext {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) (k : Fin n) (M1 M2 : Finset (Fin n)) (i : M)
    (ui vi : ℝ) : ℝ :=
  (1 - (ui - vi) * ((∑ j ∈ M1, AbarRow Atil ι i j) - ∑ j ∈ M2, AbarRow Atil ι i j) - ui - vi) /
    (1 + ∑ j ∈ M1 ∪ M2, |Abar Atil ι k j|)

/-- `v_j` for `j ∈ M2`, extended by pivoting `x_i` out with multiplier values `u_i, v_i`
(Balas §9.1, eq. (9.8), p. 111). -/
noncomputable def VExt {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (i : M) (ui vi : ℝ) (j : Fin n) : ℝ :=
  U0PlusV0Ext Atil ι k M1 M2 i ui vi * Abar Atil ι k j - (ui - vi) * AbarRow Atil ι i j

/-- `v0`, extended by pivoting `x_i` out with multiplier values `u_i, v_i` (Balas §9.1, eq. (9.8),
p. 111). -/
noncomputable def V0Ext {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (i : M) (ui vi : ℝ) : ℝ :=
  U0PlusV0Ext Atil ι k M1 M2 i ui vi * Abar0 Atil btil ι k - (ui - vi) * Abar0Row Atil btil ι i

/-- The `(CGLP)_k` objective `αx̄-β` (Balas §9.1, p. 112: `vM2 s̄M2 + vi s̄i + v0(x̄k-1)`, using the
identity `α = vÃ+v0e_k`, `β = vb̃+v0` from `(8.1)`), evaluated at the extended solution obtained
by pivoting `x_i` out with multiplier values `u_i,v_i`. -/
noncomputable def ObjExt {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (i : M) (xbar : Fin n → ℝ) (ui vi : ℝ) : ℝ :=
  (∑ j ∈ M2, VExt Atil btil ι k M1 M2 i ui vi j * SurplusM Atil btil (ι j) xbar) +
    vi * SurplusM Atil btil i xbar +
    V0Ext Atil btil ι k M1 M2 i ui vi * (xbar k - 1)

/-- `r_ui`, the reduced cost of the CGLP column `u_i` (Balas §9.1, eq. (9.6), p. 110). -/
noncomputable def ReducedCostU {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (xbar : Fin n → ℝ) (i : M) : ℝ :=
  SigmaCoef Atil btil ι k M1 M2 xbar *
    ((-(∑ j ∈ M1, AbarRow Atil ι i j) + (∑ j ∈ M2, AbarRow Atil ι i j) - 1) -
        ∑ j ∈ M2, AbarRow Atil ι i j * SurplusM Atil btil (ι j) xbar +
      Abar0Row Atil btil ι i * (1 - xbar k))

/-- `r_vi`, the reduced cost of the CGLP column `v_i` (Balas §9.1, eq. (9.6), p. 110). -/
noncomputable def ReducedCostV {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (xbar : Fin n → ℝ) (i : M) : ℝ :=
  SigmaCoef Atil btil ι k M1 M2 xbar *
    ((∑ j ∈ M1, AbarRow Atil ι i j) - (∑ j ∈ M2, AbarRow Atil ι i j) - 1 -
        ∑ j ∈ M1, AbarRow Atil ι i j * SurplusM Atil btil (ι j) xbar +
      Abar0Row Atil btil ι i * xbar k)

end Disjunctive.SimplexTableau


