-- Prove2me | Definitions.Def_Disjunctive_SimplexTableau_ReducedCost_v2
-- name    : Disjunctive_SimplexTableau_ReducedCost_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:43.03759+00:00
-- url     : https://prove2.me/theorems/127aee99-d0a4-4760-a833-24f9d06e1b8c
-- title:
--   Reduced costs $r_{u_i}, r_{v_i}$ of the CGLP columns in tableau form (corrected eq. (9.6))
-- statement:
--   For the basis of $(CGLP)_k$ with basic rows $J$ (enumerated by $\iota$; $u$-basic positions $M_1$, $v$-basic positions $M_2$) and the point $\bar x$ to be cut off ($\bar s=\tilde A\bar x-\tilde b$): the normalizing quantity $\sigma=\big(\sum_{j\in M_2}\bar a_{kj}\bar s_j-\bar a_{k0}(1-\bar x_k)\big)/\big(1+\sum_{j\in J}|\bar a_{kj}|\big)$; the extension of the basic solution when $u_i,v_i$ ($i\notin J$) are brought in (eqs. (9.7)-(9.9)) and its objective $\alpha\bar x-\beta$; and the reduced costs of eq. (9.6):
--   $$r_{u_i}=\sigma\Big(-\sum_{j\in M_1}\bar a_{ij}+\sum_{j\in M_2}\bar a_{ij}-1\Big)-\sum_{j\in M_2}\bar a_{ij}\bar s_j+\bar a_{i0}(1-\bar x_k),$$
--   $$r_{v_i}=\sigma\Big(\sum_{j\in M_1}\bar a_{ij}-\sum_{j\in M_2}\bar a_{ij}-1\Big)-\sum_{j\in M_1}\bar a_{ij}\bar s_j+\bar a_{i0}\bar x_k.$$
--
--   **Correction.** The retired transcription multiplied the whole right-hand side by $\sigma$; only the first bracket carries the factor $\sigma$ (this is the coefficient of $u_i$, $v_i$ in $\alpha\bar x-\beta$; it agrees with Balas–Perregaard (2003) and the COIN-OR `CglLandP` implementation).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §9.1, eqs. (9.6)-(9.9), pp. 109-112

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

/-- `r_ui`, the reduced cost of the CGLP column `u_i` (Balas §9.1, eq. (9.6), p. 110):
`r_ui = σ(-∑_{j∈M1} ā_ij + ∑_{j∈M2} ā_ij - 1) - ∑_{j∈M2} ā_ij s̄_j + ā_i0 (1 - x̄_k)`.
Only the first bracket is multiplied by `σ` (the retired transcription multiplied the whole
expression by `σ`, which is not the coefficient of `u_i` in `αx̄ - β`; cf. Balas–Perregaard (2003)
and the COIN-OR `CglLandP` implementation, `computeCglpRedCost`: `-σ - τ_i + (1-x̄_k)ā_i0` with
`τ_i = σ(∑_{M1} ā_ij - ∑_{M2} ā_ij) + ∑_{M2} ā_ij s̄_j`). -/
noncomputable def ReducedCostU {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (xbar : Fin n → ℝ) (i : M) : ℝ :=
  SigmaCoef Atil btil ι k M1 M2 xbar *
      (-(∑ j ∈ M1, AbarRow Atil ι i j) + (∑ j ∈ M2, AbarRow Atil ι i j) - 1) -
    (∑ j ∈ M2, AbarRow Atil ι i j * SurplusM Atil btil (ι j) xbar) +
    Abar0Row Atil btil ι i * (1 - xbar k)

/-- `r_vi`, the reduced cost of the CGLP column `v_i` (Balas §9.1, eq. (9.6), p. 110):
`r_vi = σ(∑_{j∈M1} ā_ij - ∑_{j∈M2} ā_ij - 1) - ∑_{j∈M1} ā_ij s̄_j + ā_i0 x̄_k`
(again only the first bracket is multiplied by `σ`; the form uses the tableau identity
`s̄_i = ā_i0 - ∑_{j∈J} ā_ij s̄_j` of Lemma 9.1). -/
noncomputable def ReducedCostV {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k : Fin n)
    (M1 M2 : Finset (Fin n)) (xbar : Fin n → ℝ) (i : M) : ℝ :=
  SigmaCoef Atil btil ι k M1 M2 xbar *
      ((∑ j ∈ M1, AbarRow Atil ι i j) - (∑ j ∈ M2, AbarRow Atil ι i j) - 1) -
    (∑ j ∈ M1, AbarRow Atil ι i j * SurplusM Atil btil (ι j) xbar) +
    Abar0Row Atil btil ι i * xbar k

end Disjunctive.SimplexTableau


