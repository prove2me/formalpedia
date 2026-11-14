-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Constants
-- name    : ConsistentSubmodular_Randomized_Constants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:25.344072+00:00
-- url     : https://prove2.me/theorems/69535744-24f8-4fad-80b2-91ea1348f8fb
-- title:
--   Constants of the randomized threshold: quartic $Q$, $q=(1-\xi^\star)/\xi^\star$, and the root $u_1$ of $\Phi$
-- statement:
--   Constants used in Section 2 and Appendix A for the randomized ratio $\xi^\star\approx0.7942$ (the root of $\Psi$ in $(1/2,1)$) and the polynomial $\Phi(x)=x^4+x^3-2x^2-3x+2$.
--
--   - `quartic` $t$: $Q(t)=t^4+t^3-22t^2-87t+24$, so that $Q(t)=(1+t)^4\,\Psi\bigl(1/(1+t)\bigr)$.
--   - `qStar`: $q=(1-\xi^\star)/\xi^\star$.
--   - `uOne`: the weight $u_1$, a root of $\Phi$ in $(0,1)$, chosen via the existence of such a root (it is unique, being the only zero of the strictly decreasing $\Phi$ on $[0,1]$).
--
--   The file also proves the basic facts that make these definitions meaningful: continuity and the derivative $\Phi'(x)=4x^3+3x^2-4x-3=(x^2-1)(4x+3)$, strict monotonicity of $\Phi$ on $[0,1]$, existence of a root in $(0,1)$ from $\Phi(0)=2>0>-1=\Phi(1)$, the properties $0<u_1<1$ and $\Phi(u_1)=0$, and the numerical bounds $1/2<u_1<3/5$.
--
--   These constants parametrize the extremal consecutive-interval instance and the chain estimates of Appendix A that identify $\xi^\star$ as the optimal adaptivity gap.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Constants.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- `Q(t) = t⁴ + t³ - 22 t² - 87 t + 24`, so that `Q(t) = (1 + t)⁴ Ψ(1/(1 + t))`. -/
def quartic (t : ℝ) : ℝ := t ^ 4 + t ^ 3 - 22 * t ^ 2 - 87 * t + 24

/-- The number `q = (1 - ξ⋆) / ξ⋆`. -/
def qStar : ℝ := (1 - xiStar) / xiStar

theorem continuous_phi : Continuous phi := by
  unfold phi
  fun_prop

theorem hasDerivAt_phi (x : ℝ) :
    HasDerivAt phi (4 * x ^ 3 + 3 * x ^ 2 - 4 * x - 3) x := by
  have h := ((((hasDerivAt_pow 4 x).add (hasDerivAt_pow 3 x)).sub
    ((hasDerivAt_pow 2 x).const_mul (2 : ℝ))).sub ((hasDerivAt_id x).const_mul (3 : ℝ)))
  refine (h.add_const (2 : ℝ)).congr_deriv ?_
  norm_num
  ring

/-- `Φ'(x) = (x² - 1)(4x + 3) < 0` on `(0, 1)`, so `Φ` is strictly decreasing on
`[0, 1]`. -/
theorem phi_strictAntiOn : StrictAntiOn phi (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_phi.continuousOn
  rw [interior_Icc]
  intro x hx
  rw [(hasDerivAt_phi x).deriv]
  have h : 4 * x ^ 3 + 3 * x ^ 2 - 4 * x - 3 = (x ^ 2 - 1) * (4 * x + 3) := by ring
  rw [h]
  apply mul_neg_of_neg_of_pos _ (by linarith [hx.1])
  nlinarith [hx.1, hx.2]

/-- `Φ(0) = 2 > 0 > -1 = Φ(1)`, so `Φ` has a root in `(0, 1)`. -/
theorem exists_phi_root : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ phi u = 0 := by
  have hsub := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num) continuous_phi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (phi 1) (phi 0) := by
    constructor <;> norm_num [phi]
  obtain ⟨u, ⟨h0, h1⟩, hu⟩ := hsub hmem
  exact ⟨u, h0, h1, hu⟩

/-- The weight `u₁`, the root of `Φ` in `(0, 1)`. -/
def uOne : ℝ := exists_phi_root.choose

theorem uOne_pos : 0 < uOne := exists_phi_root.choose_spec.1

theorem uOne_lt_one : uOne < 1 := exists_phi_root.choose_spec.2.1

theorem phi_uOne : phi uOne = 0 := exists_phi_root.choose_spec.2.2

/-- `1/2 < u₁ < 3/5`, from `Φ(1/2) > 0 > Φ(3/5)`. -/
theorem uOne_bounds : (1 : ℝ) / 2 < uOne ∧ uOne < 3 / 5 := by
  have hmem : uOne ∈ Set.Icc (0 : ℝ) 1 := ⟨uOne_pos.le, uOne_lt_one.le⟩
  constructor
  · by_contra h
    have hle : uOne ≤ 1 / 2 := le_of_not_gt h
    have hmono := phi_strictAntiOn.antitoneOn hmem ⟨by norm_num, by norm_num⟩ hle
    have : (0 : ℝ) < phi (1 / 2) := by norm_num [phi]
    linarith [phi_uOne]
  · by_contra h
    have hle : (3 : ℝ) / 5 ≤ uOne := le_of_not_gt h
    have hmono := phi_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩ hmem hle
    have : phi (3 / 5) < (0 : ℝ) := by norm_num [phi]
    linarith [phi_uOne]

end ConsistentSubmodular.Chains

end


