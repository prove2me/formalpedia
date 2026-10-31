-- Prove2me | Definitions.Def_FiniteStateContract_Equivalence_Model
-- name    : FiniteStateContract_Equivalence_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:14:05.824194+00:00
-- url     : https://prove2.me/theorems/76139983-5933-4de0-9d41-ef86129a008e
-- title:
--   Contracts, controlled finite-state laws, Hamiltonians, and Nash equilibria
-- statement:
--   Let $m$ be the finite number of states, $T\ge0$ the duration, $A\subseteq\mathbb R^l$ a compact action set, and $p^\circ$ an arbitrary probability vector, possibly on the boundary of the simplex. Reuse the canonical space of càdlàg finite-state paths continuous at $T$, its coordinate filtration, the unit-rate reference law $P$, and the explicit jump-product density. States are basis-vector labels; the population remains infinite and time continuous.
--
--   The data are the rates $q$, agent running cost $c$, utilities $u,U$, and principal costs $c_0,C_0$. Assumption 2.1 means zero row sums, uniformly bounded positive off-diagonal rates, and a uniform Lipschitz bound in action and population distribution. It does not impose a uniform positive lower bound. The Hamiltonian is
--   $$H_i(t,z,a,p,R)=c(t,i,a,p)-R+\sum_{j\ne i}(z_j-z_i)(q(t,i,j,a,p)-1).$$
--   Assumption 3.1 requires an actual unique action minimizer $\hat a_i(t,z,p)$, measurable in its arguments and uniformly Lipschitz in $z$ for the state seminorm. The minimized Hamiltonian evaluates $H_i$ at that minimizer. This reads the extra hat on the right side of (15) as the unminimized function, as its arity and the preceding sentence require.
--
--   Admissible controls and running payments are all predictable processes. A contract's terminal payment is measurable and in $L^2(P)$; its utility is not assumed square integrable. Both costs are the exact signed extended expectations in (7)–(8), with all integral domains exposed. A Nash equilibrium is an admissible best response against every admissible control, with measurable flow starting at $p^\circ$ and pointwise marginal consistency. Contracts in $\mathcal C$ have at least one equilibrium. No terminal-state-only, bounded-payment, or Markov-policy restriction is imposed.
-- source:
--   Carmona and Wang, Finite-State Contract Theory with a Principal and a Field of Agents, held PDF arXiv:1808.07942v1 (23 Aug 2018), §§2–3.1, (1)–(19), Definition 2.2, Assumptions 2.1 and 3.1, PDF pp. 3–6 = printed pp. 3–6; catalog DOI 10.1287/mnsc.2020.3760 (metadata basis published).

import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_FiniteStateContract_Equivalence_Integration

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FiniteStateContract.Equivalence
noncomputable section

open ExtFSMFG.Existence (Omega Xc Xm filt Q0 IsReference seminormE densityR)

abbrev Vec (m : ℕ) := Fin m → ℝ
abbrev Action (l : ℕ) := EuclideanSpace ℝ (Fin l)
abbrev Proc (m : ℕ) (T : ℝ≥0) (B : Type*) := ℝ≥0 → Omega m T → B
abbrev Flow (m : ℕ) := ℝ≥0 → Vec m
abbrev Feedback (m l : ℕ) := ℝ≥0 → Fin m → Vec m → Vec m → Action l

/-- The §2 data, without additional regularity, utility-invertibility or
solvability assumptions. The simplex inhabitant retains boundary initial laws. -/
structure Data (m l : ℕ) (T : ℝ≥0) where
  A : Set (Action l)
  p₀ : stdSimplex ℝ (Fin m)
  P : Measure (Omega m T)
  q : ℝ≥0 → Fin m → Fin m → Action l → Vec m → ℝ
  c : ℝ≥0 → Fin m → Action l → Vec m → ℝ
  u : ℝ → ℝ
  U : ℝ → ℝ
  c₀ : ℝ≥0 → Vec m → ℝ
  C₀ : Vec m → ℝ

variable {m l : ℕ} {T : ℝ≥0}

/-- Compact actions and the canonical unit-rate probability law of §2.2. -/
def Setting (D : Data m l T) : Prop :=
  IsCompact D.A ∧ IsProbabilityMeasure D.P ∧ IsReference T D.p₀ D.P

/-- Assumption 2.1, including only strict pointwise positivity, no uniform lower bound. -/
def Assumption21 (D : Data m l T) : Prop :=
  (∀ t ≤ T, ∀ i, ∀ a ∈ D.A, ∀ p ∈ stdSimplex ℝ (Fin m), ∑ j, D.q t i j a p = 0) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ t ≤ T, ∀ i j, i ≠ j → ∀ a ∈ D.A,
    ∀ p ∈ stdSimplex ℝ (Fin m), 0 < D.q t i j a p ∧ D.q t i j a p ≤ C) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ t ≤ T, ∀ i j, ∀ a ∈ D.A, ∀ a' ∈ D.A,
    ∀ p ∈ stdSimplex ℝ (Fin m), ∀ p' ∈ stdSimplex ℝ (Fin m),
      |D.q t i j a p - D.q t i j a' p'| ≤
        C * (‖a - a'‖ + Real.sqrt (∑ k, (p k - p' k)^2)))

/-- The Hamiltonian (12)–(13), evaluated on basis state `i`. -/
def H (D : Data m l T) (t : ℝ≥0) (i : Fin m) (z : Vec m)
    (a : Action l) (p : Vec m) (R : ℝ) : ℝ :=
  D.c t i a p - R + ∑ j ∈ Finset.univ.erase i, (z j - z i) * (D.q t i j a p - 1)

/-- Assumption 3.1: actual unique minimization of H, measurability, and the
uniform seminorm Lipschitz estimate in z only. The reward argument is arbitrary. -/
def Assumption31 (D : Data m l T) (a : Feedback m l) : Prop :=
  (∀ t ≤ T, ∀ i z, ∀ p ∈ stdSimplex ℝ (Fin m), a t i z p ∈ D.A ∧
    ∀ R, ∀ b ∈ D.A, b ≠ a t i z p → H D t i z (a t i z p) p R < H D t i z b p R) ∧
  (∀ i, Measurable fun x : Set.Icc (0 : ℝ≥0) T × Vec m × stdSimplex ℝ (Fin m) =>
    a x.1 i x.2.1 x.2.2) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ t ≤ T, ∀ i z z', ∀ p ∈ stdSimplex ℝ (Fin m),
    ‖a t i z p - a t i z' p‖ ≤ C * seminormE i (z - z'))

/-- Equation (15), reading the RHS function name as H (the five-argument function). -/
def Hhat (D : Data m l T) (a : Feedback m l) (t : ℝ≥0) (i : Fin m)
    (z : Vec m) (p : Vec m) (R : ℝ) : ℝ := H D t i z (a t i z p) p R

def IsControl (D : Data m l T) (α : Proc m T (Action l)) : Prop :=
  IsStronglyPredictable (filt m T) α ∧ ∀ t ≤ T, ∀ ω, α t ω ∈ D.A

/-- Frozen-flow statements allow every measurable simplex-valued flow. -/
def IsFlow (p : Flow m) : Prop :=
  (Measurable fun t : Set.Icc (0 : ℝ≥0) T => p t) ∧
    ∀ t ≤ T, p t ∈ stdSimplex ℝ (Fin m)

structure Contract (m : ℕ) (T : ℝ≥0) where
  r : Proc m T ℝ
  ξ : Omega m T → ℝ

/-- Payments have precisely the regularity in §2.3; U(ξ) is not assumed L². -/
def IsContract (D : Data m l T) (K : Contract m T) : Prop :=
  IsStronglyPredictable (filt m T) K.r ∧ Measurable K.ξ ∧ MemLp K.ξ 2 D.P

def rateField (D : Data m l T) (α : Proc m T (Action l)) (p : Flow m) :=
  fun t ω i j => D.q t i j (α t ω) (p t)

/-- The explicit Doléans exponential, with no normalization. -/
def controlledLaw (D : Data m l T) (α : Proc m T (Action l)) (p : Flow m) :=
  D.P.withDensity fun ω => ENNReal.ofReal (densityR T (rateField D α p) ω)

/-- Definedness of the raw density construction. These are not data hypotheses:
whenever a theorem asserts a controlled cost, it must establish these conditions. -/
def LawDefined (D : Data m l T) (α : Proc m T (Action l)) (p : Flow m) : Prop :=
  (∀ᵐ ω ∂D.P, IntegrableOn (fun t : ℝ =>
    ∑ j ∈ Finset.univ.erase (Xm t.toNNReal ω),
      (D.q t.toNNReal (Xm t.toNNReal ω) j (α t.toNNReal ω) (p t.toNNReal) - 1))
      (Set.Icc 0 T)) ∧
  AEMeasurable (densityR T (rateField D α p)) D.P ∧
  (∀ᵐ ω ∂D.P, 0 ≤ densityR T (rateField D α p) ω) ∧
  IsProbabilityMeasure (controlledLaw D α p)

/-- A running plus terminal cost, using signed extended integrals at both levels. -/
def RunningCostValue (Q : Measure (Omega m T)) (f : Proc m T ℝ)
    (g : Omega m T → ℝ) (v : EReal) : Prop :=
  ∃ I : Omega m T → EReal,
    (∀ᵐ ω ∂Q, IntegralValue (volume.restrict (Set.Icc (0 : ℝ) T))
      (fun t => (f t.toNNReal ω : EReal)) (I ω)) ∧
    IntegralValue Q (fun ω => I ω + (g ω : EReal)) v

/-- Equation (7), evaluated under the controlled law, with definedness exposed. -/
def AgentCost (D : Data m l T) (K : Contract m T) (α : Proc m T (Action l))
    (p : Flow m) (v : EReal) : Prop :=
  LawDefined D α p ∧ RunningCostValue (controlledLaw D α p)
    (fun t ω => D.c t (Xc t ω) (α t ω) (p t) - D.u (K.r t ω))
    (fun ω => -D.U (K.ξ ω)) v

/-- Equation (8). -/
def PrincipalCost (D : Data m l T) (K : Contract m T) (α : Proc m T (Action l))
    (p : Flow m) (v : EReal) : Prop :=
  LawDefined D α p ∧ RunningCostValue (controlledLaw D α p)
    (fun t ω => D.c₀ t (p t) + K.r t ω) (fun ω => D.C₀ (p T) + K.ξ ω) v

/-- Every competing control is evaluated; undefined competitors are not omitted. -/
def Optimal (D : Data m l T) (K : Contract m T) (α : Proc m T (Action l))
    (p : Flow m) : Prop :=
  IsControl D α ∧ ∃ v, AgentCost D K α p v ∧
    ∀ β, IsControl D β → ∃ w, AgentCost D K β p w ∧ v ≤ w

/-- Definition 2.2: full-history best response and pointwise marginal consistency. -/
def Nash (D : Data m l T) (K : Contract m T) (α : Proc m T (Action l))
    (p : Flow m) : Prop :=
  IsFlow (T := T) p ∧ p 0 = D.p₀.1 ∧ Optimal D K α p ∧
    ∀ t ≤ T, ∀ i, controlledLaw D α p {ω | Xc t ω = i} = ENNReal.ofReal (p t i)

/-- Contracts in C, §2.6. -/
def AdmissibleContract (D : Data m l T) (K : Contract m T) : Prop :=
  IsContract D K ∧ ∃ α p, Nash D K α p

end
end FiniteStateContract.Equivalence


