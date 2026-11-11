-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_CSPReduction
-- name    : QuantumSepPoly_Frobenius_CSPReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:11.511998+00:00
-- url     : https://prove2.me/theorems/2e7c0ba2-3313-4a58-b065-9a2f925932d4
-- title:
--   The projected flat dense CSP construction
-- statement:
--   Compute $D=\Pi(C_{\rm flat})$, $\gamma=d^2\|D\|_{\max}$, $\Omega=E\times E$, and $s=\gamma\kappa^4+2\lambda(\kappa^2+1)^2+1$. For four independent symbol slots, define
--   $$P_{a,b,c,e}=\tfrac12+\frac{\operatorname{Re}(d^2D_{ac,be}\bar x_ax_b\bar y_cy_e)-\lambda(|x_a|^2-1)(|x_b|^2-1)-\lambda(|y_c|^2-1)(|y_e|^2-1)}{2s}.$$
--   Every ordered quadruple is a constraint. Repeated variable indices receive the same assigned symbol when evaluating a constraint. The construction assumes no predicate-range or optimum-approximation guarantee; those are separate theorems.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 19 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DenseCSP
import Definitions.Def_QuantumSepPoly_Frobenius_DiskNet
import Definitions.Def_QuantumSepPoly_Frobenius_FlatDecomposition

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- §5.2 (iv)–(v), p.19: projection after entrywise thresholding. -/
def reductionD {d : ℕ} (p : FlatParameters) (δ : ℝ) (M : Bip d) (U V : Op d) : Bip d :=
  project (flatPart p δ (centered M) U V)

def reductionGamma {d : ℕ} (D : Bip d) : ℝ := (d : ℝ)^2 * maxEntry D

def cspScale (γ η : ℝ) : ℝ :=
  γ * (discKappa γ η)^4 + 2 * discLambda γ η * ((discKappa γ η)^2+1)^2 + 1

/-- Four independent argument slots; repeated variable indices receive equal symbols
only when evaluating an assignment, exactly as in Definition 5.1. -/
def reductionPredicate {d : ℕ} (D : Bip d) (η : ℝ) (t : Fin 4 → Fin d)
    (z : Fin 4 → ℂ × ℂ) : ℝ :=
  let γ := reductionGamma D
  1/2 + (( (d : ℂ)^2 * D (t 0,t 2) (t 1,t 3) *
      star (z 0).1 * (z 1).1 * star (z 2).2 * (z 3).2).re -
    discLambda γ η * (‖(z 0).1‖^2-1) * (‖(z 1).1‖^2-1) -
    discLambda γ η * (‖(z 2).2‖^2-1) * (‖(z 3).2‖^2-1)) / (2*cspScale γ η)

abbrev ReductionSymbol (γ η : ℝ) := {z : ℂ × ℂ // z.1 ∈ alphabet γ η ∧ z.2 ∈ alphabet γ η}

instance reductionSymbolFintype (γ η : ℝ) : Fintype (ReductionSymbol γ η) := by
  classical
  exact Fintype.ofEquiv (↥(alphabet γ η) × ↥(alphabet γ η))
    { toFun := fun z => ⟨(z.1.val,z.2.val),z.1.property,z.2.property⟩
      invFun := fun z => (⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩)
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }

def reductionInstance {d : ℕ} (hd : 0 < d) (D : Bip d) (η : ℝ) :
    MaxCSP d 4 (ReductionSymbol (reductionGamma D) η) where
  constraints := Finset.univ
  nonempty := ⟨fun _ => ⟨0,hd⟩, Finset.mem_univ _⟩
  predicate t z := reductionPredicate D η t (fun i => (z i).val)

end QuantumSepPoly.Frobenius


