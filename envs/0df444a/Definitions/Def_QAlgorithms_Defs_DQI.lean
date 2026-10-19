-- Prove2me | Definitions.Def_QAlgorithms_Defs_DQI
-- name    : QAlgorithms_Defs_DQI
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:04:48.903662+00:00
-- url     : https://prove2.me/theorems/7e5ca136-e3c0-46ff-8e20-9b0f22ac39e8
-- title:
--   max-LINSAT and decoded quantum interferometry (shared definition layer)
-- statement:
--   # max-LINSAT and decoded quantum interferometry (shared definition layer)
--
--   S. P. Jordan et al., *Optimization by decoded quantum interferometry* (arXiv:2408.08292v5),
--   cited "DQI p.N" (PDF pages), §§2, 4, 8, 9.
--
--   Conventions. `F_p = ZMod p`; the instance is `B ∈ F_p^{m×n}` (`Matrix (Fin m) (Fin n) (ZMod p)`,
--   row `i` is `b_i`) and the sets `F_i ⊆ F_p`; an assignment is `x : Fin n → ZMod p`, and the DQI
--   state lives on `EuclideanSpace ℂ (Fin n → ZMod p)` (computational basis `|x⟩`).
--   -/
--
--   namespace QAlgorithms
--
--   open scoped Matrix
--
--   /-- DQI p.4 (Definition 2.1), p.26: `s(x)`, the number of satisfied max-LINSAT constraints
--   `b_i · x ∈ F_i`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DQI.lean

import Definitions.Def_QAlgorithms_Defs_LaurentQSP
/-!
# max-LINSAT and decoded quantum interferometry (shared definition layer)

S. P. Jordan et al., *Optimization by decoded quantum interferometry* (arXiv:2408.08292v5),
cited "DQI p.N" (PDF pages), §§2, 4, 8, 9.

Conventions. `F_p = ZMod p`; the instance is `B ∈ F_p^{m×n}` (`Matrix (Fin m) (Fin n) (ZMod p)`,
row `i` is `b_i`) and the sets `F_i ⊆ F_p`; an assignment is `x : Fin n → ZMod p`, and the DQI
state lives on `EuclideanSpace ℂ (Fin n → ZMod p)` (computational basis `|x⟩`).
-/

namespace QAlgorithms

open scoped Matrix

/-- DQI p.4 (Definition 2.1), p.26: `s(x)`, the number of satisfied max-LINSAT constraints
`b_i · x ∈ F_i`. -/
def linsatSatisfied {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : ℕ :=
  (Finset.univ.filter fun i => B.mulVec x i ∈ F i).card

/-- DQI p.11, §8.2.1 p.21: the objective `f(x) = Σ_i f_i(b_i · x)` with `f_i = +1` on
`F_i = f_i⁻¹(+1)` and `−1` off it (so `f(x) = 2 s(x) − m`). -/
def linsatObjective {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : ℤ :=
  ∑ i, if B.mulVec x i ∈ F i then 1 else -1

/-- DQI pp.11, 22: the DQI state `|P(f)⟩ = Σ_x P(f(x)) |x⟩`, unnormalized (normalization is a
side condition of the statements, as in Lemma 9.2). -/
noncomputable def dqiState {p m n : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (P : Polynomial ℂ) : EuclideanSpace ℂ (Fin n → ZMod p) :=
  WithLp.toLp 2 fun x => P.eval (linsatObjective B F x : ℂ)

/-- DQI p.11 (Theorem 4.1), §9.4 p.34: the optimal expected number `⟨s⟩` of satisfied
constraints of the symbol string obtained by measuring a normalized DQI state `|P(f)⟩` in the
computational basis, over polynomials `P` of degree `⩽ ℓ` (`Σ_x |⟨x|ψ⟩|² s(x)`, the frozen
`densityMean ∘ pureDensity`). The set is non-empty (a suitable constant `P`) and bounded above by
`m`, so `sSup` is the true supremum. -/
noncomputable def dqiOptimalSatisfied {p m n : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ P : Polynomial ℂ, P.natDegree ≤ ℓ ∧ ‖dqiState B F P‖ = 1 ∧
    s = densityMean (pureDensity (dqiState B F P)) (fun x => (linsatSatisfied B F x : ℝ))}

/-- DQI pp.10–11: `t < d^⊥`, every non-zero codeword of `C^⊥ = {d ∈ F_p^m : Bᵀ d = 0}` has
Hamming weight `> t` (used with `t = 2ℓ + 1`). -/
def DualDistanceExceeds {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p)) (t : ℕ) : Prop :=
  ∀ d : Fin m → ZMod p, d ≠ 0 → Bᵀ.mulVec d = 0 → t < hammingNorm d

/-- DQI p.11, Eq. (9): the semicircle law
`⟨s⟩/m = (√(μ(1 − ρ)) + √(ρ(1 − μ)))²` if `ρ ⩽ 1 − μ`, and `1` otherwise (`μ = ℓ/m`, `ρ = r/p`). -/
noncomputable def semicircleValue (μ ρ : ℝ) : ℝ :=
  if ρ ≤ 1 - μ then (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2 else 1

/-! ### Sanity tests -/

example {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    linsatSatisfied B (fun _ => Finset.univ) x = m := by
  simp [linsatSatisfied]

example {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    linsatObjective B (fun _ => ∅) x = -(m : ℤ) := by
  simp [linsatObjective]

example {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 3)) (t : ℕ) (hB : DualDistanceExceeds B t)
    (d : Fin m → ZMod 3) (hd : hammingNorm d ≤ t) (h0 : Bᵀ.mulVec d = 0) : d = 0 := by
  by_contra h
  exact absurd (hB d h h0) (not_lt.2 hd)

example (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : semicircleValue 0 ρ = ρ := by
  simp [semicircleValue, h1, Real.sq_sqrt h0]

example (μ ρ : ℝ) (h : 1 - μ < ρ) : semicircleValue μ ρ = 1 := by
  simp [semicircleValue, not_le.2 h]

example {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (F : Fin m → Finset (ZMod 2))
    (x : Fin n → ZMod 2) : dqiState B F 1 x = 1 := by
  simp [dqiState]

end QAlgorithms


