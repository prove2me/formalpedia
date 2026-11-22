-- Prove2me | Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
-- name    : Formalism_DegreeFormula_FlagDegFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:21.210507+00:00
-- url     : https://prove2.me/theorems/527f5116-a932-49ed-9f19-cf2680310e9b
-- title:
--   Flag Deg Formula
-- statement:
--   Definitions and structural lemmas for Flag Deg Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/FlagDegFormula.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace Formalism.DegreeFormula
def dimFl (ι : Type) [Fintype ι] (N : ℕ) : ℕ := Fintype.card ι * (N * (N - 1) / 2)
def permExp {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) : (ι × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))
def degFl (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ dimFl ι N *
    ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (permExp σ)
def linRoot {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) : MvPolynomial (ι × Fin N) ℝ :=
  -∑ x : ι × Fin N, C (lam x.1 x.2) * X x
def flagDeg (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ) : ℝ :=
  degFl ι N (linRoot lam ^ dimFl ι N)
def weylProd {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) : ℝ :=
  ∏ τ, ∏ i : Fin N, ∏ k : Fin N, if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1
def FlagDegFormula : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (lam : ι → Fin N → ℝ),
    flagDeg ι N lam = (Nat.factorial (dimFl ι N) : ℝ) * weylProd lam
def DegFlAnti : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (a b : Fin N) (P : MvPolynomial (ι × Fin N) ℝ),
    a ≠ b →
      degFl ι N (rename (fun x : ι × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) P) =
        -degFl ι N P
def DegFlPowerSum : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    1 ≤ k → degFl ι N ((∑ i : Fin N, X (τ, i) ^ k) * P) = 0
def DegFlPoint : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ),
    degFl ι N (∏ x : ι × Fin N, (-X x) ^ (N - 1 - (x.2 : ℕ))) = 1
def DegFlMul : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (N : ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) (Q : MvPolynomial (κ × Fin N) ℝ),
    degFl (ι ⊕ κ) N (rename (fun x : ι × Fin N => ((Sum.inl x.1 : ι ⊕ κ), x.2)) P *
      rename (fun x : κ × Fin N => ((Sum.inr x.1 : ι ⊕ κ), x.2)) Q) = degFl ι N P * degFl κ N Q
def DegFlEsymm : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (k : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    1 ≤ k → degFl ι N (rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P) = 0
def DegFlHomog : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (d : ℕ) (P : MvPolynomial (ι × Fin N) ℝ),
    P.IsHomogeneous d → d ≠ dimFl ι N → degFl ι N P = 0
end Formalism.DegreeFormula


