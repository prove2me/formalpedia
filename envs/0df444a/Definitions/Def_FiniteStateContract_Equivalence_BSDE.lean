-- Prove2me | Definitions.Def_FiniteStateContract_Equivalence_BSDE
-- name    : FiniteStateContract_Equivalence_BSDE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:14:40.587058+00:00
-- url     : https://prove2.me/theorems/888fa0da-586c-4dff-907a-537c6adafea3
-- title:
--   Backward equations, equilibrium dynamics, and the printed forward control class
-- statement:
--   The backward solution class consists of adapted càdlàg $Y$ and adapted left-continuous $Z$ with $E^P\int_0^T Y_t^2dt<\infty$ and $E^P\int_0^T\|Z_t\|_{X_{t-}}^2dt<\infty$. The stochastic integral is the exact finite jump sum minus its compensator, using the published tail-integral primitive; its ordinary integral must be defined. Equations hold outside one null set simultaneously for every time.
--
--   The frozen and optimized drivers are respectively $H(s,X_{s-},Z_s,\alpha_s,p(s),u(r_s))$ and $\hat H(s,X_{s-},Z_s,p(s),u(r_s))$, with terminal value $-U(\xi)$. This explicitly reads $r_t$ in (20)–(21) as $r_s$, consistently with (7), (22), (26), (27), and (30). The missing time differentials in Definition 3.5 are ordinary time integration. Uniqueness means indistinguishable $Y$ and zero expected integrated squared seminorm of the difference of the two $Z$ processes.
--
--   The mean-field backward predicate includes all of (22)–(25): the optimized BSDE, feedback control, the explicit Doléans density, and marginal consistency under the resulting probability law. The forward predicate uses (30)–(33), with arbitrary initial random variable and the same law equations. Its input class retains the first power $E^P\int_0^T\|Z_t\|_{X_{t-}}dt<\infty$ printed on p. 8. It does not impose the backward second moment or square integrability of a reconstructed payment.
--
--   The feedback control is extended by zero after $T$ so that its global predictability depends only on the source data on $[0,T]$.
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), §§3.1–3.3, (20)–(33), Definition 3.5, PDF pp. 6–9 = printed pp. 6–9; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_FiniteStateContract_Equivalence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FiniteStateContract.Equivalence
noncomputable section

open ExtFSMFG.Existence (Omega Xc Xm filt Q0 seminormE stochIntM)
variable {m l : ℕ} {T : ℝ≥0}

/-- Adaptedness only on the source time interval. -/
def AdaptedOn {B : Type*} [TopologicalSpace B] (Y : Proc m T B) : Prop :=
  ∀ t ≤ T, StronglyMeasurable[filt m T t] (Y t)

def CadlagOn (Y : Proc m T ℝ) : Prop :=
  ∀ ω, (∀ t < T, ContinuousWithinAt (fun s => Y s ω) (Set.Ici t) t) ∧
    ∀ t ≤ T, 0 < t → ∃ y, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 y)

def LeftContinuousOn (Z : Proc m T (Vec m)) : Prop :=
  ∀ ω, ∀ t ≤ T, ContinuousWithinAt (fun s => Z s ω) (Set.Iic t) t

/-- Expected time-integrated seminorm moment, of power k. -/
def ZMoment (P : Measure (Omega m T)) (Z : Proc m T (Vec m)) (k : ℕ) : Prop :=
  (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (seminormE (Xm t.toNNReal ω) (Z t.toNNReal ω) ^ k)) ∂P) < ∞

/-- Definition 3.5 uses the second moment. -/
def BackwardRegular (P : Measure (Omega m T)) (Y : Proc m T ℝ)
    (Z : Proc m T (Vec m)) : Prop :=
  AdaptedOn Y ∧ CadlagOn Y ∧ AdaptedOn Z ∧ LeftContinuousOn Z ∧
  (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Y t.toNNReal ω ^ 2)) ∂P) < ∞ ∧
  ZMoment P Z 2

/-- Domain of the compensated finite-jump integral: no default-zero Bochner drift. -/
def StochDefined (Z : Proc m T (Vec m)) (ω : Omega m T) : Prop :=
  IntegrableOn (fun t : ℝ => ∑ j, Z t.toNNReal ω j * Q0 m j (Xm t.toNNReal ω))
    (Set.Icc 0 T)

/-- Prefix integral obtained by subtracting two tails of the published exact jump integral. -/
def stochPrefix (Z : Proc m T (Vec m)) (t : ℝ≥0) (ω : Omega m T) : ℝ :=
  stochIntM T Z 0 ω - stochIntM T Z t ω

/-- A BSDE with terminal reward -U(ξ), including the domains of its real integrals.
The equations hold outside one null set, simultaneously for all times. -/
def Backward (D : Data m l T) (K : Contract m T)
    (F : ℝ≥0 → Omega m T → Vec m → ℝ)
    (Y : Proc m T ℝ) (Z : Proc m T (Vec m)) : Prop :=
  BackwardRegular D.P Y Z ∧ ∀ᵐ ω ∂D.P,
    StochDefined Z ω ∧
    IntegrableOn (fun s : ℝ => F s.toNNReal ω (Z s.toNNReal ω)) (Set.Icc 0 T) ∧
    ∀ t ≤ T, Y t ω = -D.U (K.ξ ω) +
      (∫ s in Set.Ioc (t : ℝ) T, F s.toNNReal ω (Z s.toNNReal ω)) - stochIntM T Z t ω

def frozenDriver (D : Data m l T) (K : Contract m T)
    (α : Proc m T (Action l)) (p : Flow m) :=
  fun t ω z => H D t (Xm t ω) z (α t ω) (p t) (D.u (K.r t ω))

def optimizedDriver (D : Data m l T) (a : Feedback m l)
    (r : Proc m T ℝ) (p : Flow m) :=
  fun t ω z => Hhat D a t (Xm t ω) z (p t) (D.u (r t ω))

/-- (17)/(24), an actual history-dependent feedback from Z on [0,T].
The fixed zero extension after T keeps arbitrary out-of-domain data from affecting predictability. -/
def feedbackControl (a : Feedback m l) (Z : Proc m T (Vec m)) (p : Flow m) :
    Proc m T (Action l) := fun t ω => if t ≤ T then a t (Xm t ω) (Z t ω) (p t) else 0

/-- Uniqueness modulo indistinguishability of Y and the seminorm-integral quotient of Z. -/
def UniqueBackward (D : Data m l T) (K : Contract m T)
    (F : ℝ≥0 → Omega m T → Vec m → ℝ) : Prop :=
  ∀ Y Z Y' Z', Backward D K F Y Z → Backward D K F Y' Z' →
    (∀ᵐ ω ∂D.P, ∀ t ≤ T, Y t ω = Y' t ω) ∧
    (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (seminormE (Xm t.toNNReal ω)
        (Z t.toNNReal ω - Z' t.toNNReal ω) ^ 2)) ∂D.P) = 0

/-- Equations (23), (25) (also (31), (33)), using the explicit solution of the
Doléans exponential equation from the published rate-density construction. -/
def LawConsistency (D : Data m l T) (α : Proc m T (Action l)) (p : Flow m)
    (Q : Measure (Omega m T)) : Prop :=
  LawDefined D α p ∧ Q = controlledLaw D α p ∧ IsProbabilityMeasure Q ∧
  IsFlow (T := T) p ∧ p 0 = D.p₀.1 ∧
  ∀ t ≤ T, ∀ i, Q {ω | Xc t ω = i} = ENNReal.ofReal (p t i)

/-- Definition 3.5, all of (22)–(25). -/
def MeanFieldBackward (D : Data m l T) (a : Feedback m l) (K : Contract m T)
    (Y : Proc m T ℝ) (Z : Proc m T (Vec m)) (α : Proc m T (Action l))
    (p : Flow m) (Q : Measure (Omega m T)) : Prop :=
  Backward D K (optimizedDriver D a K.r p) Y Z ∧ IsControl D α ∧
  (∀ᵐ ω ∂D.P, ∀ t ≤ T, α t ω = feedbackControl a Z p t ω) ∧
  LawConsistency D α p Q

/-- The forward H²_X as actually printed on p. 8: first power, not second power. -/
def ForwardZ (D : Data m l T) (Z : Proc m T (Vec m)) : Prop :=
  AdaptedOn Z ∧ LeftContinuousOn Z ∧ ZMoment D.P Z 1

/-- Forward dynamics (30)–(33), with no square-integrability imposed on Y or the
recovered terminal payment. The source's control class is kept in full. -/
def Forward (D : Data m l T) (a : Feedback m l) (Z : Proc m T (Vec m))
    (r : Proc m T ℝ) (Y₀ : Omega m T → ℝ) (Y : Proc m T ℝ)
    (α : Proc m T (Action l)) (p : Flow m) (Q : Measure (Omega m T)) : Prop :=
  AdaptedOn Y ∧ CadlagOn Y ∧ IsControl D α ∧ LawConsistency D α p Q ∧
  ∀ᵐ ω ∂D.P, StochDefined Z ω ∧
    IntegrableOn (fun s : ℝ => optimizedDriver D a r p s.toNNReal ω (Z s.toNNReal ω))
      (Set.Icc 0 T) ∧
    ∀ t ≤ T, α t ω = feedbackControl a Z p t ω ∧
      Y t ω = Y₀ ω -
        (∫ s in Set.Ioc (0 : ℝ) t, optimizedDriver D a r p s.toNNReal ω (Z s.toNNReal ω)) +
        stochPrefix Z t ω

end
end FiniteStateContract.Equivalence


