-- Prove2me | Definitions.Def_AggCG_Supplement_parityTrapMILP
-- name    : AggCG_Supplement_parityTrapMILP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:22:32.642352+00:00
-- url     : https://prove2.me/theorems/8efa904e-bf36-45d6-ae4a-fed1d30a59b8
-- title:
--   Perturbed parity-trap MILP $Q^\eta$
-- statement:
--   $Q^\eta(k_1,\ldots,k_n)$ is the mixed-binary parity-trap program (4): selector variables, odd parity blocks, and continuous trap variables, with every designated nonzero objective, coefficient, or right-hand-side entry independently multiplied by $1+\eta$ while supports, boxes, row types, and integrality remain fixed.
--
--   The accompanying controller uses dyadic comparisons, exhausts activated traps, and otherwise follows the continuing spine.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), eq. (4) and §E.3, pp.29–30, PDF pp.30–31

import Mathlib
import Definitions.Def_AggCG_Supplement_MILP

namespace AggCG.Supplement

/-- The variables of the parity-trap MILP (4) with `n = T + 1` blocks of sizes `k` (Sharma, *Computational
Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC
2027 submission (manuscript sha256 f7ea0248…), §E.3, p.29, PDF p.30): selectors `x_j`, parity variables
`y_{j,a}` (`a < k_j`) and `t_h`, `0`-based. -/
abbrev EVar (T : ℕ) (k : Fin (T + 1) → ℕ) := Fin (T + 1) ⊕ (Σ j : Fin (T + 1), Fin (k j)) ⊕ Fin (T + 1)

namespace EVar

variable {T : ℕ} {k : Fin (T + 1) → ℕ}

/-- Selector `x_j`. -/
def x (j : Fin (T + 1)) : EVar T k := Sum.inl j
/-- Parity variable `y_{j,a}`. -/
def y (j : Fin (T + 1)) (a : Fin (k j)) : EVar T k := Sum.inr (Sum.inl ⟨j, a⟩)
/-- `t_h`. -/
def t (h : Fin (T + 1)) : EVar T k := Sum.inr (Sum.inr h)
/-- Being a parity variable. -/
def IsY (v : EVar T k) : Prop := ∃ j a, v = y j a

end EVar

/-- An entrywise multiplicative perturbation of (4) (p.29: "replaces each designated nonzero coefficient
or RHS entry v of the objective and these displayed constraints by v(1 + η), with |η| ≤ ε. Entries may
have distinct perturbations"): one `η` per designated nonzero entry. Field names follow the rows:
objective (`objT`, `objX`); `t_h ≤ 2x_h` (`capT`, `capX`); `t_h + 3x_j ≤ 2` for `j ≤ h` (`exT`, `exX`,
`exR`, indexed `j h`); `2 Σ_a y_{j,a} = k_j x_j` (`parY`, `parX`); `y_{j,a} ≤ 2x_j` (`ubY`, `ubX`). -/
structure TrapPert (T : ℕ) (k : Fin (T + 1) → ℕ) where
  /-- Objective coefficient of `t_h`. -/
  objT : Fin (T + 1) → ℝ
  /-- Objective coefficient of `x_j`. -/
  objX : Fin (T + 1) → ℝ
  /-- Coefficient of `t_h` in `t_h ≤ 2x_h`. -/
  capT : Fin (T + 1) → ℝ
  /-- Coefficient of `x_h` in `t_h ≤ 2x_h`. -/
  capX : Fin (T + 1) → ℝ
  /-- Coefficient of `t_h` in `t_h + 3x_j ≤ 2`. -/
  exT : Fin (T + 1) → Fin (T + 1) → ℝ
  /-- Coefficient of `x_j` in `t_h + 3x_j ≤ 2`. -/
  exX : Fin (T + 1) → Fin (T + 1) → ℝ
  /-- Right-hand side of `t_h + 3x_j ≤ 2`. -/
  exR : Fin (T + 1) → Fin (T + 1) → ℝ
  /-- Coefficient of `y_{j,a}` in the parity equality. -/
  parY : (j : Fin (T + 1)) → Fin (k j) → ℝ
  /-- Coefficient of `x_j` in the parity equality. -/
  parX : Fin (T + 1) → ℝ
  /-- Coefficient of `y_{j,a}` in `y_{j,a} ≤ 2x_j`. -/
  ubY : (j : Fin (T + 1)) → Fin (k j) → ℝ
  /-- Coefficient of `x_j` in `y_{j,a} ≤ 2x_j`. -/
  ubX : (j : Fin (T + 1)) → Fin (k j) → ℝ

/-- Every perturbation has magnitude at most `ε`. -/
def TrapPert.Bounded {T : ℕ} {k : Fin (T + 1) → ℕ} (η : TrapPert T k) (ε : ℝ) : Prop :=
  (∀ h, |η.objT h| ≤ ε) ∧ (∀ j, |η.objX j| ≤ ε) ∧ (∀ h, |η.capT h| ≤ ε) ∧ (∀ h, |η.capX h| ≤ ε) ∧
    (∀ j h, |η.exT j h| ≤ ε) ∧ (∀ j h, |η.exX j h| ≤ ε) ∧ (∀ j h, |η.exR j h| ≤ ε) ∧
    (∀ j a, |η.parY j a| ≤ ε) ∧ (∀ j, |η.parX j| ≤ ε) ∧ (∀ j a, |η.ubY j a| ≤ ε) ∧
    (∀ j a, |η.ubX j a| ≤ ε)

/-- The zero perturbation (the idealized unperturbed program). -/
def TrapPert.zero (T : ℕ) (k : Fin (T + 1) → ℕ) : TrapPert T k :=
  ⟨0, 0, 0, 0, 0, 0, 0, fun _ _ => 0, 0, fun _ _ => 0, fun _ _ => 0⟩

open EVar in
/-- The perturbed program `Q^η(k_1, …, k_n)` of (4) (p.29): maximize `Σ_h t_h − (1/10) Σ_j x_j` subject to
`t_h ≤ 2x_h`, `t_h + 3x_j ≤ 2` (`j ≤ h`), `2 Σ_a y_{j,a} = k_j x_j`, `y_{j,a} ≤ 2x_j`, every designated
nonzero entry `v` replaced by `v(1 + η)`; `x, y` binary, `t_h ∈ [−2, 2]`. Supports, row types, boxes and
integrality are not perturbed. -/
noncomputable def parityTrapMILP (T : ℕ) (k : Fin (T + 1) → ℕ) (η : TrapPert T k) : MILP (EVar T k) where
  obj := fun v => match v with
    | Sum.inl j => -(1 / 10) * (1 + η.objX j)
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr h) => 1 + η.objT h
  rows :=
    ((List.finRange (T + 1)).map fun h =>
        ((fun v => if v = t h then 1 + η.capT h else if v = x h then -2 * (1 + η.capX h) else 0),
          false, (0 : ℝ))) ++
    ((List.finRange (T + 1)).flatMap fun h => ((List.finRange (T + 1)).filter fun j => j ≤ h).map fun j =>
        ((fun v => if v = t h then 1 + η.exT j h else if v = x j then 3 * (1 + η.exX j h) else 0),
          false, 2 * (1 + η.exR j h))) ++
    ((List.finRange (T + 1)).map fun j =>
        ((fun v : EVar T k => match v with
            | Sum.inr (Sum.inl ⟨j', a⟩) => if j' = j then 2 * (1 + η.parY j' a) else 0
            | Sum.inl j' => if j' = j then -(k j : ℝ) * (1 + η.parX j) else 0
            | _ => 0), true, (0 : ℝ))) ++
    ((List.finRange (T + 1)).flatMap fun j => (List.finRange (k j)).map fun a =>
        ((fun v => if v = y j a then 1 + η.ubY j a else if v = x j then -2 * (1 + η.ubX j a) else 0),
          false, (0 : ℝ)))
  lo := fun v => match v with | Sum.inr (Sum.inr _) => -2 | _ => 0
  hi := fun v => match v with | Sum.inr (Sum.inr _) => 2 | _ => 1
  isBin := fun v => match v with | Sum.inr (Sum.inr _) => false | _ => true

end AggCG.Supplement


