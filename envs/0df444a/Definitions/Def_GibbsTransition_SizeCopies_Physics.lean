-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Physics
-- name    : GibbsTransition_SizeCopies_Physics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:51:44.069465+00:00
-- url     : https://prove2.me/theorems/6cd98952-a0d6-4db2-900b-d7daa4a5819b
-- title:
--   Translated interactions, Gibbs and ground states, and the phase class
-- statement:
--   An interaction consists of an on-site $3\times3$ matrix and three directed $9\times9$ edge matrices. Admissibility means every matrix is Hermitian, has algebraic entries, and has Euclidean operator norm at most one. There is no commutativity restriction.
--
--   For every real control field $\phi\in[0,1]$, set
--
--   $$H_{u,L}(\phi)=\sum_x(h_0)_x+\sum_{i=1}^3\sum_{x,x+e_i\in\Lambda_L}(h_i)_{x,x+e_i}-\phi M_L+B_L.$$
--
--   The Gibbs density is $e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$. The ground density is the entire least-eigenspace projector divided by its trace. The finite order parameter is $L^{-3}\operatorname{tr}(\rho^\infty M_L)$.
--
--   The phase promise requires a target $\theta\in[1/4,3/4]$ and convergence of the ground order parameter at every real field other than $\theta$. Every left-side limit is in $[0,1/4]$ and every right-side limit is in $[3/4,1]$. The class $\mathcal C^*$ is admissibility plus existence of such a target. The target is selected from this promise, not from a supplied oracle. Its uniqueness and thermodynamic energy convergence remain proof obligations.
--
--   The file also defines the actual ferromagnet (18), the Born probability of its $C$-containing sector, and the full function $\xi_{\beta,R}$ of (30). These definitions supply the physical content for the lower-bound construction.
--
--   **Formalization Note** Finite spectral functional calculus defines the ground projector and matrix exponential, including noncommuting Hamiltonians. Least energies use the real spectral infimum only on nonempty Hermitian matrices. Off-domain defaults are not physical instances. Energy and target selection use existence-based choice; no convergence or separation theorem is assumed as an interaction field.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §2, Equations (2)–(7), printed pp. 3–4 (PDF pp. 5–6); §4.1, Equation (18), printed p. 7 (PDF p. 9); §5.2, Equation (30), printed p. 10 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Lattice
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GibbsTransition.SizeCopies

attribute [local instance] Classical.propDecidable

/-- Raw translated terms. Norm/algebraicity are separately checked predicates. -/
structure Interaction where
  onsite : QutritMatrix
  edge : Fin 3 → EdgeMatrix

/-- Exactly the source's Hermitian algebraic terms, each bounded in Euclidean
operator norm by J=1. No commutativity hypothesis. -/
def Admissible (u : Interaction) : Prop :=
  u.onsite.IsHermitian ∧ (∀ i, (u.edge i).IsHermitian) ∧
  (∀ s t, IsAlgebraic ℚ (u.onsite s t)) ∧
  (∀ i s t, IsAlgebraic ℚ (u.edge i s t)) ∧
  ‖u.onsite‖ ≤ 1 ∧ ∀ i, ‖u.edge i‖ ≤ 1

def bulkHamiltonian (u : Interaction) (L : ℕ) : CubeMatrix L :=
  (∑ x : Site L, atSite u.onsite x) +
    ∑ i : Fin 3, ∑ xy ∈ internalEdges L i, atEdge (u.edge i) xy.1 xy.2

def hamiltonian (u : Interaction) (L : ℕ) (phi : ℝ) : CubeMatrix L :=
  bulkHamiltonian u L - phi • magnetization L + boundaryTerm L

/-- Least spectral value on Hermitian nonempty matrices. The source uses this
only for L≥1; the spectrum is finite, nonempty and bounded there. -/
noncomputable def leastEnergy {L : ℕ} (A : CubeMatrix L) : ℝ :=
  sInf (spectrum ℝ A)

/-- Full least-eigenspace projector, with no choice of ground vector.
Finite spectral functional calculus works for this discontinuous function. -/
noncomputable def groundProjector {L : ℕ} (A : CubeMatrix L) : CubeMatrix L := by
  classical
  exact cfc (fun x : ℝ => if x = leastEnergy A then 1 else 0) A

noncomputable def groundDensity (u : Interaction) (L : ℕ) (phi : ℝ) : CubeMatrix L :=
  ((Matrix.trace (groundProjector (hamiltonian u L phi)))⁻¹) •
    groundProjector (hamiltonian u L phi)

/-- Actual noncommutative matrix exponential, with complex physical amplitudes. -/
noncomputable def gibbsDensity (u : Interaction) (L : ℕ) (phi beta : ℝ) : CubeMatrix L :=
  let W := cfc (fun x : ℝ => Real.exp (-beta*x)) (hamiltonian u L phi)
  (Matrix.trace W)⁻¹ • W

noncomputable def finiteEnergy (u : Interaction) (L : ℕ) (phi : ℝ) : ℝ :=
  leastEnergy (hamiltonian u L phi) / (L : ℝ) ^ 3

noncomputable def groundOrder (u : Interaction) (L : ℕ) (phi : ℝ) : ℝ :=
  (Matrix.trace (groundDensity u L phi * magnetization L)).re / (L : ℝ) ^ 3

/-- Entire-side phase promise on real physical fields. Existence of the energy
limit is deliberately not an assumption. `n+1` avoids using the empty cube. -/
def PhasePromise (u : Interaction) (theta : ℝ) : Prop :=
  theta ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) ∧
  ∀ phi ∈ Set.Icc (0 : ℝ) 1, phi ≠ theta →
    ∃ m : ℝ, Filter.Tendsto (fun n : ℕ => groundOrder u (n+1) phi)
      Filter.atTop (nhds m) ∧
      (phi < theta → m ∈ Set.Icc (0 : ℝ) (1 / 4)) ∧
      (theta < phi → m ∈ Set.Icc (3 / 4 : ℝ) 1)

def InClass (u : Interaction) : Prop := Admissible u ∧ ∃ theta, PhasePromise u theta

/-- A target extracted from the promise, never supplied by a state oracle.
Uniqueness is a separate proof obligation. The fallback is off the model class. -/
noncomputable def transitionPoint (u : Interaction) : ℝ :=
  if h : ∃ theta, PhasePromise u theta then h.choose else 0

/-- Thermodynamic energy selected by convergence. Existence, uniqueness and the
surface error remain proof obligations; no oracle/structure field supplies them. -/
noncomputable def limitingEnergy (u : Interaction) (phi : ℝ) : ℝ :=
  if h : ∃ e : ℝ, Filter.Tendsto (fun n : ℕ => finiteEnergy u (n+1) phi)
    Filter.atTop (nhds e) then h.choose else 0

/-- Equation (18), including its ordered, diagonal 9×9 interaction. -/
def ferromagnet (r : ℝ) : Interaction where
  onsite := Matrix.diagonal fun s => if s = 0 then 0 else
    if s = 1 then (1 / 2 : ℂ) else ((1 / 2 - r : ℝ) : ℂ)
  edge := fun _ => Matrix.diagonal fun s => if s.1 = s.2 then 0 else (kappa : ℂ)

/-- Born probability of the C-containing sector of the actual Gibbs state. -/
noncomputable def excitedProbability (r : ℝ) (L : ℕ) (phi beta : ℝ) : ℝ :=
  ∑ s : Configuration L, if ∃ x, s x = 2 then
    (gibbsDensity (ferromagnet r) L phi beta s s).re else 0

noncomputable def xi (beta : ℝ) (R : ℕ) : ℝ :=
  ((12 * (R : ℝ)^3)^6 / (Nat.factorial 6 : ℝ)) * Real.exp (-2*kappa*beta) *
    Real.exp ((R : ℝ)^3 * Real.exp (-kappa*beta) +
      12*(R : ℝ)^3 * Real.exp (-kappa*beta/3))

end GibbsTransition.SizeCopies


