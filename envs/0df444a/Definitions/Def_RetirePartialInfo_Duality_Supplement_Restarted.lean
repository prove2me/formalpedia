-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Supplement_Restarted
-- name    : RetirePartialInfo_Duality_Supplement_Restarted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:20:39.263698+00:00
-- url     : https://prove2.me/theorems/ffebf17b-9bc7-4a20-9258-65288a06424f
-- title:
--   Theorem 3.3 context — actual inverse, extended contact boundary and restarted budget-feasible primal controls
-- statement:
--   Let $v$ and $f$ be the post-retirement PDE and retirement VI functions. Set $\widehat v=v+f-\ell(1-e^{\beta(t-T_1)})/\beta$ for $t\le T_1$, and $\widehat v=v$ afterward. The multiplier is the actual inverse of the increasing marginal $\partial_y\widehat v$, with its existence established in the theorem.
--
--   $$\Xi(t,p)=\sup\{y>0:f(t,y,p)=g(t,y)\}\in[0,\infty],\quad \tau^*=\inf\{s\in[t,T_1]:y_s\le\Xi(s,p_s)\}\wedge T_1.$$
--
--   The supremum is extended: empty contact gives 0 and unbounded contact gives $\infty$. Thus the zero-income and terminal contact sets do not require an invented finite maximum. Consumption and bequest use the published inverse marginal utility.
--
--   The restarted primal problem uses the published plan object with elapsed time. Feasibility requires initial wealth $x$, the wealth floor, all conditional budget inequalities under $\widetilde P$, and all observation-adapted competitors. The Stieltjes term in a budget interval is its atom on $(u,v]$; the candidate's initial budget cost counts the atom even at immediate retirement.
--
--   Optimality means existence of a feasible wealth process with the prescribed terminal bequest and a greatest objective over the full feasible set. This definition does not assert that the proposed controls have that property.
--
--   **Formalization Note** Positive consumption/bequest and finite objective/budget integrability follow the published base conventions. Real suprema are avoided for the boundary and optimum. The hitting-time infimum includes the finite mandatory cap, so its defining set is nonempty and bounded.
--
--   At the mandatory date the full contact supremum is $\infty$. For $\xi>0$ the source instead assigns the left limit $\ell/\xi$ to its terminal boundary (Proposition 3.3, pp.23–24). These terminal values give the same capped retirement time; we retain the full contact supremum consistently.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 8–12, (8), (10), (13)–(18); pp. 17,22–26, (33), (55), Theorem 3.3

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_HMM

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

variable {Sample : Type} [MeasurableSpace Sample]

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), pp.17,24–26, (33), Theorem 3.3.
**Formalization Note.** The post-mandatory-date branch of (33) is retained. -/
noncomputable def vhat (a : Data) (v f : Value) : Value :=
  fun t y p => if t ≤ a.par.T1 then v t y p + f t y p - laborCost a t else v t y p

/-- The inverse of the increasing marginal dual value, pp.24–25.
Only used after its positive unique root is established in the theorem. -/
noncomputable def inverseMarginal (v : Value) (t z p : ℝ) : ℝ :=
  sInf {y : ℝ | 0 < y ∧ z ≤ dy v t y p}

/-- Logarithmic and reverse-time coordinates of (40),(54), pp.20,22. -/
noncomputable def logValue (a : Data) (f : Value) (zeta z p : ℝ) : ℝ :=
  f (a.par.T1-zeta) (Real.exp z) p

noncomputable def gap (a : Data) (f : Value) (zeta z p : ℝ) : ℝ :=
  logValue a f zeta z p - obstacle a (a.par.T1-zeta) (Real.exp z)

def adjustmentRegion (a : Data) (f : Value) : Set Space :=
  {z | z 0 ∈ Ioc 0 a.par.T1 ∧ z 2 ∈ Ioo 0 1 ∧ gap a f (z 0) (z 1) (z 2) = 0}

def nonadjustmentRegion (a : Data) (f : Value) : Set Space :=
  {z | z 0 ∈ Ioc 0 a.par.T1 ∧ z 2 ∈ Ioo 0 1 ∧ 0 < gap a f (z 0) (z 1) (z 2)}

/-- Extended contact-set threshold; (55), p.22.
**Formalization Note.** This is the supremum of positive contact y values, in [0,∞].
It agrees with exp(max contact log y) when that maximum exists. Empty contact has threshold
0; unbounded contact has threshold ∞. At T1 and for the zero-income solution f=g the
threshold is ∞ and retirement is immediate. For ξ>0 this terminal contact value differs
from Proposition 3.3's left limit ℓ/ξ (pp.23–24); the capped hitting time is identical
under either terminal convention. No positive-income restriction is added. -/
noncomputable def threshold (a : Data) (f : Value) (t p : ℝ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {y : ℝ | 0 < y ∧ f t y p = obstacle a t y})

/-- Elapsed-time form of the source's first boundary hitting time, capped at T1.
The cap is included in the infimum's set, so there is no empty real infimum. -/
noncomputable def hit (a : Data) (m : HMMFamily Sample) (f : Value) (t p y : ℝ)
    (sample : Sample) : ℝ≥0 :=
  sInf ({u : ℝ≥0 | (u : ℝ) ≤ max (a.par.T1-t) 0 ∧
    ENNReal.ofReal (dualPath a m t p y (t+u) sample) ≤
      threshold a f (t+u) (beliefPath m t p (t+u) sample)} ∪
    { (max (a.par.T1-t) 0).toNNReal })

noncomputable def consumption (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (u : ℝ≥0) (sample : Sample) : ℝ :=
  Iinv (crra a) (t+u) (dualPath a m t p y (t+u) sample)

noncomputable def bequest (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (sample : Sample) : ℝ :=
  Iinv (crra a) a.par.T (dualPath a m t p y a.par.T sample)

noncomputable def reward (a : Data) (t : ℝ) (q : Plan Sample) (u : ℝ)
    (sample : Sample) : ℝ :=
  Real.exp (-a.par.β*u) *
    (crra a (t+u) (q.c u.toNNReal sample) - a.par.ℓ * (1-Rind q.τ u.toNNReal sample))

noncomputable def objective (a : Data) (m : HMMFamily Sample) (t p : ℝ)
    (q : Plan Sample) : ℝ :=
  ∫ sample, (∫ u in Icc (0 : ℝ) (a.par.T-t), reward a t q u sample) +
    Real.exp (-a.par.β*(a.par.T-t)) * crra a a.par.T (q.H (a.par.T-t).toNNReal sample)
    ∂(m.market t p).P

noncomputable def restartAtom (a : Data) (t : ℝ) (rho : Sample → ℝ≥0)
    (u v : ℝ≥0) (sample : Sample) : ℝ :=
  if u < rho sample ∧ rho sample ≤ v then
    b a.par (t+rho sample) / Bt a.par (t+rho sample) else 0

noncomputable def restartBudgetLHS (a : Data) (t : ℝ) (q : Plan Sample)
    (u v : ℝ≥0) (sample : Sample) : ℝ :=
  (q.H v sample - b a.par (t+v) * (1-Rind q.τ v sample)) / Bt a.par (t+v) +
    (∫ s in Ioc (u : ℝ) v, q.c s.toNNReal sample / Bt a.par (t+s)) -
    restartAtom a t q.τ u v sample

/-- Restart of the full budget-feasible choice problem (8),(10), pp.8–10, at calendar t.
**Formalization Note.** `Plan` is the immutable base object, with an elapsed-time index.
The wealth floor, all conditional budget inequalities, and the (u,v] retirement atom
are retained. Consumption and terminal wealth are strictly positive and the budget/objective
integrands integrable, as in the published base model. Only [0,T-t] is constrained.
The initial wealth is x; it is not renamed x-b(t). All stopping times use F^S. -/
def feasible (a : Data) (m : HMMFamily Sample) (t p x : ℝ) (q : Plan Sample) : Prop :=
  let st := m.market t p
  let h := a.par.T-t
  let Q := Pt a.par st (m.integralTheta t p)
  Stops a m t p q.τ ∧
  Measurable (fun z : ℝ≥0 × Sample => q.c (min z.1 h.toNNReal) z.2) ∧
  (∀ u : ℝ≥0, (u : ℝ) ≤ h → Measurable[FS a.par st u] (q.c u)) ∧
  (∀ u : ℝ≥0, (u : ℝ) ≤ h → ∀ sample, 0 < q.c u sample) ∧
  (∀ᵐ sample ∂st.P, IntegrableOn (fun u : ℝ => q.c u.toNNReal sample) (Icc 0 h)) ∧
  (∀ u : ℝ≥0, (u : ℝ) ≤ h → Measurable[FS a.par st u] (q.H u)) ∧
  (∀ᵐ sample ∂st.P, q.H 0 sample = x) ∧
  (∀ u : ℝ≥0, (u : ℝ) ≤ h →
    ∀ᵐ sample ∂st.P, (1-Rind q.τ u sample) * b a.par (t+u) ≤ q.H u sample) ∧
  (∀ u v : ℝ≥0, u < v → (v : ℝ) ≤ h →
    Integrable (restartBudgetLHS a t q u v) Q ∧
    Q[restartBudgetLHS a t q u v | FS a.par st u] ≤ᵐ[Q]
      fun sample => (q.H u sample - b a.par (t+u)*(1-Rind q.τ u sample)) / Bt a.par (t+u)) ∧
  (∀ᵐ sample ∂st.P, 0 < q.H h.toNNReal sample) ∧
  Integrable (fun z : ℝ × Sample => reward a t q z.1 z.2)
    ((volume.restrict (Icc (0 : ℝ) h)).prod st.P) ∧
  Integrable (fun sample => crra a a.par.T (q.H h.toNNReal sample)) st.P

/-- Candidate budget cost (17), with its initial atom counted also at immediate retirement.
The multiplier in Theorem 3.3 must satisfy X=x-b(t); this is a conclusion, not a hypothesis. -/
noncomputable def candidateCost (a : Data) (m : HMMFamily Sample) (t p y : ℝ)
    (rho : Sample → ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (Bt a.par t) *
    ∫⁻ sample, ENNReal.ofReal (bequest a m t p y sample / Bt a.par a.par.T) +
      (∫⁻ u in Icc (0 : ℝ) (a.par.T-t),
        ENNReal.ofReal (consumption a m t p y u.toNNReal sample / Bt a.par (t+u))) +
      ENNReal.ofReal (-b a.par (t+rho sample) / Bt a.par (t+rho sample))
      ∂Pt a.par (m.market t p) (m.integralTheta t p)

/-- Primal optimality includes a feasible wealth process and domination over every
observation-adapted feasible competitor, not merely the displayed control formulas. -/
def OptimalControls (a : Data) (m : HMMFamily Sample) (f : Value) (t p x y : ℝ) : Prop :=
  ∃ H : ℝ≥0 → Sample → ℝ,
    let q : Plan Sample := ⟨consumption a m t p y, H, hit a m f t p y⟩
    feasible a m t p x q ∧
    (H (a.par.T-t).toNNReal =ᵐ[(m.market t p).P] bequest a m t p y) ∧
    IsGreatest {v : ℝ | ∃ competitor : Plan Sample,
      feasible a m t p x competitor ∧ v = objective a m t p competitor}
      (objective a m t p q)

end RetirePartialInfo.Duality.Supplement


