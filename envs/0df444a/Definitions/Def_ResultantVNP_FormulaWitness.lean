-- Prove2me | Definitions.Def_ResultantVNP_FormulaWitness
-- name    : ResultantVNP_FormulaWitness
-- status  : Definition
-- author  : @gjindal
-- created : 2026-11-14T21:24:31.831504+00:00
-- url     : https://prove2.me/theorems/ff8f189d-dbd0-447f-b712-9aab6166e432
-- title:
--   Arithmetic formulas and Boolean-sum witnesses for VP
-- statement:
--   A binary arithmetic formula over the complex numbers, its gate count and polynomial value, and the property that every bounded-degree polynomial-size circuit family can be expressed as a Boolean sum of polynomial-size formulas. The witness variables are appended to the original variables and range over 0 and 1.
-- source:
--   Valiant, Completeness classes in algebra, STOC 1979; see also Hrubeš, Wigderson and Yehudayoff, Relationless completeness and separations, Theorem 11 and Section IV-A, https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HWY10_rel/HWY10_rel_proc.pdf.

import Definitions.Def_ResultantVNP_VP

namespace PermanentFoundation

open MvPolynomial

/-- A binary arithmetic formula over the complex numbers. -/
inductive Formula (σ : Type) where
  | var (i : σ)
  | const (c : ℂ)
  | add (p q : Formula σ)
  | mul (p q : Formula σ)

def Formula.size {σ : Type} : Formula σ → ℕ
  | .var _ | .const _ => 0
  | .add p q | .mul p q => p.size + 1 + q.size

noncomputable def Formula.value {σ : Type} : Formula σ → MvPolynomial σ ℂ
  | .var i => X i
  | .const c => C c
  | .add p q => p.value + q.value
  | .mul p q => p.value * q.value

end PermanentFoundation

namespace VNPNestedBooleanSum

open MvPolynomial PermanentFoundation

noncomputable def witnessEval (a q : ℕ) (y : Fin q → Fin 2) :
    MvPolynomial (Fin (a + q)) ℂ →ₐ[ℂ] MvPolynomial (Fin a) ℂ :=
  aeval (Fin.append (fun i : Fin a => X i)
    (fun j : Fin q => C (((y j).val : ℂ))))

/-- Polynomial-size formula witnesses whose Boolean sums represent VP. -/
def VPFormulaSumProperty : Prop :=
  ∀ g ∈ ResultantVNP.VP, ∃ r : ℕ → ℕ, ResultantVNP.PolyBounded r ∧
    ∃ F : ∀ n, Formula (Fin (g.nvars n + r n)),
      ResultantVNP.PolyBounded (fun n => (F n).size) ∧
      ∀ n, g.p n = ∑ z : Fin (r n) → Fin 2,
        witnessEval (g.nvars n) (r n) z (F n).value

end VNPNestedBooleanSum


