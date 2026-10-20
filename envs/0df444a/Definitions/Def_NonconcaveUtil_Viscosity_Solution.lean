-- Prove2me | Definitions.Def_NonconcaveUtil_Viscosity_Solution
-- name    : NonconcaveUtil_Viscosity_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:04.588892+00:00
-- url     : https://prove2.me/theorems/0a935746-0b00-41a4-ab51-baa0b407c38b
-- title:
--   Definition A.1 — viscosity subsolutions and supersolutions with terminal asymptotics
-- statement:
--   A locally bounded function $V(t,w)$ is tested on $[0,T)\times(B,\infty)$. Its upper and lower semicontinuous envelopes are $V^*$ and $V_*$, while $H^*$ and $H_*$ are the corresponding envelopes of the portfolio Hamiltonian
--
--   $$H(w,p,A)=\sup_{d\le\pi\le u}\left\{\tfrac12\pi^2w^2\sigma^2A+\pi w\eta p\right\}.$$
--
--   A subsolution uses smooth functions touching $V^*$ from above and the inequality $-\psi_t\le H^*$; a supersolution uses functions touching $V_*$ from below and $H_*\le-\varphi_t$. Both carry the liquidation boundary condition (13). For bounded portfolio bounds they carry the special terminal profile (15), which combines the left limit of $U$ with a standard normal distribution function. For unbounded bounds the terminal target is the concave envelope $\hat U$ in (18). A viscosity solution satisfies both sets of conditions.
--
--   This definition specifies the solution class in the comparison and uniqueness theorems.
--
--   **Formalization Note** Envelopes and terminal limits approach through $D=[0,T)\times(B,\infty)$. Hamiltonians use extended reals so an unbounded supremum remains infinite. Smooth test functions are $C^\infty$ on the real plane. The terminal clauses are stated for $w>B$, and also for $w=B$ when $U(B)$ is finite. The finite-width formula is evaluated only in the bounded branch.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), pp. 27–28 (PDF 27–28), Appendix A, Definition A.1, (20)–(28)

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- The upper semicontinuous envelope of (20), approached from the PDE domain. -/
noncomputable def upperEnv (mk : Market) (V : ℝ → ℝ → ℝ) (t w : ℝ) : EReal :=
  limsup (fun p : ℝ × ℝ => (V p.1 p.2 : EReal)) (𝓝[mk.D] (t, w))

noncomputable def lowerEnv (mk : Market) (V : ℝ → ℝ → ℝ) (t w : ℝ) : EReal :=
  liminf (fun p : ℝ × ℝ => (V p.1 p.2 : EReal)) (𝓝[mk.D] (t, w))

def LocallyBounded (mk : Market) (V : ℝ → ℝ → ℝ) : Prop :=
  ∀ p ∈ mk.D, ∃ C : ℝ, ∀ᶠ q : ℝ × ℝ in 𝓝[mk.D] p, |V q.1 q.2| ≤ C

/-- Hamiltonian (21); EReal retains an infinite supremum. -/
noncomputable def Ham (mk : Market) (w p A : ℝ) : EReal :=
  ⨆ π ∈ mk.Weights,
    (((1 / 2 : ℝ) * π ^ 2 * w ^ 2 * mk.sigma ^ 2 * A + π * w * mk.eta * p) : EReal)

noncomputable def Hup (mk : Market) (w p A : ℝ) : EReal :=
  limsup (fun x : ℝ × ℝ × ℝ => Ham mk x.1 x.2.1 x.2.2) (𝓝 (w, p, A))

noncomputable def Hlow (mk : Market) (w p A : ℝ) : EReal :=
  liminf (fun x : ℝ × ℝ × ℝ => Ham mk x.1 x.2.1 x.2.2) (𝓝 (w, p, A))

def UtilityDomain (mk : Market) (bc : BdryCase) : Set ℝ :=
  match bc with
    | .finite => Set.Ici mk.B
    | .crra _ _ _ => Set.Ioi mk.B

/-- The least concave majorant of U on its true domain. Under Assumption 3.1 the
majorant family is nonempty and its pointwise values are bounded below by U. -/
noncomputable def Uhat (mk : Market) (U : ℝ → ℝ) (bc : BdryCase) (w : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ g : ℝ → ℝ, ConcaveOn ℝ (UtilityDomain mk bc) g ∧
    (∀ x ∈ UtilityDomain mk bc, U x ≤ g x) ∧ v = g w}

noncomputable def K (mk : Market) (U : ℝ → ℝ) (bc : BdryCase) (w : ℝ) : ℝ :=
  by classical exact if mk.Bounded then U w else Uhat mk U bc w

/-- `K(w−)`; the prescribed boundary convention is `K(B−)=K(B)`. -/
noncomputable def Kminus (mk : Market) (U : ℝ → ℝ) (bc : BdryCase) (w : ℝ) : ℝ :=
  if w = mk.B then K mk U bc w
  else sSup (K mk U bc '' Set.Ioo mk.B w)

/-- Standard normal distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x

/-- The expression subtracted from V in the bounded-portfolio terminal condition. -/
noncomputable def terminalProfile (mk : Market) (U : ℝ → ℝ) (bc : BdryCase)
    (w t ζ : ℝ) : ℝ :=
  Kminus mk U bc w +
    2 * Phi (min 0 (Real.log (ζ / w)) / (mk.L * Real.sqrt (mk.T - t))) *
      (K mk U bc w - Kminus mk U bc w)

/-- Definition A.1(i), including the boundary and terminal clauses. -/
def IsViscositySubsolution (mk : Market) (U : ℝ → ℝ) (bc : BdryCase)
    (V : ℝ → ℝ → ℝ) : Prop :=
  LocallyBounded mk V ∧
  (∀ ψ : ℝ → ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ψ) →
    (∀ q ∈ mk.D, upperEnv mk V q.1 q.2 ≤ (ψ q.1 q.2 : EReal)) →
    ∀ t w : ℝ, (t, w) ∈ mk.D → upperEnv mk V t w = (ψ t w : EReal) →
      ((-deriv (fun s => ψ s w) t : ℝ) : EReal) ≤
        Hup mk w (deriv (fun x => ψ t x) w)
          (deriv (deriv (fun x => ψ t x)) w)) ∧
  (∀ t ∈ Set.Ico 0 mk.T,
    match bc with
      | .finite => upperEnv mk V t mk.B ≤ (U mk.B : EReal)
      | .crra pTilde A1 A2 =>
          limsup (fun q : ℝ × ℝ =>
            ((V q.1 q.2 - VCRRA mk pTilde A1 A2 q.1 q.2 : ℝ) : EReal))
            (𝓝[mk.D] (t, 0)) ≤ 0) ∧
  (∀ w : ℝ, mk.B < w ∨ (w = mk.B ∧ bc = .finite) →
    (mk.Bounded →
      limsup (fun q : ℝ × ℝ =>
        ((V q.1 q.2 - terminalProfile mk U bc w q.1 q.2 : ℝ) : EReal))
        (𝓝[mk.D] (mk.T, w)) ≤ 0) ∧
    (¬mk.Bounded → upperEnv mk V mk.T w ≤ (Uhat mk U bc w : EReal)))

/-- Definition A.1(ii), with the lower Hamiltonian envelope. -/
def IsViscositySupersolution (mk : Market) (U : ℝ → ℝ) (bc : BdryCase)
    (V : ℝ → ℝ → ℝ) : Prop :=
  LocallyBounded mk V ∧
  (∀ ψ : ℝ → ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry ψ) →
    (∀ q ∈ mk.D, (ψ q.1 q.2 : EReal) ≤ lowerEnv mk V q.1 q.2) →
    ∀ t w : ℝ, (t, w) ∈ mk.D → lowerEnv mk V t w = (ψ t w : EReal) →
      Hlow mk w (deriv (fun x => ψ t x) w)
        (deriv (deriv (fun x => ψ t x)) w) ≤
          ((-deriv (fun s => ψ s w) t : ℝ) : EReal)) ∧
  (∀ t ∈ Set.Ico 0 mk.T,
    match bc with
      | .finite => (U mk.B : EReal) ≤ lowerEnv mk V t mk.B
      | .crra pTilde A1 A2 =>
          0 ≤ liminf (fun q : ℝ × ℝ =>
            ((V q.1 q.2 - VCRRA mk pTilde A1 A2 q.1 q.2 : ℝ) : EReal))
            (𝓝[mk.D] (t, 0))) ∧
  (∀ w : ℝ, mk.B < w ∨ (w = mk.B ∧ bc = .finite) →
    (mk.Bounded →
      0 ≤ liminf (fun q : ℝ × ℝ =>
        ((V q.1 q.2 - terminalProfile mk U bc w q.1 q.2 : ℝ) : EReal))
        (𝓝[mk.D] (mk.T, w))) ∧
    (¬mk.Bounded → (Uhat mk U bc w : EReal) ≤ lowerEnv mk V mk.T w))

def IsViscositySolution (mk : Market) (U : ℝ → ℝ) (bc : BdryCase)
    (V : ℝ → ℝ → ℝ) : Prop :=
  IsViscositySubsolution mk U bc V ∧ IsViscositySupersolution mk U bc V

end NonconcaveUtil.Viscosity


