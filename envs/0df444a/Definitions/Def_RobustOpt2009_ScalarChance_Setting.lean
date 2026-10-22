-- Prove2me | Definitions.Def_RobustOpt2009_ScalarChance_Setting
-- name    : RobustOpt2009_ScalarChance_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:44.953396+00:00
-- url     : https://prove2.me/theorems/06b4b0bf-67ba-4052-a462-230ffb023a8e
-- title:
--   Scalar chance constraints and bounded moment uncertainty sets
-- statement:
--   For finite-dimensional real vectors, this module defines the affine residual of (2.2.1), robust feasibility as a universal inequality over a concrete uncertainty set, and the probability of the strict event $z_0+\sum_i\zeta_i z_i>0$. P.2 is represented by finite exponential expectations bounded by $\exp(\max\{\mu_i^-t,\mu_i^+t\}+\sigma_i^2t^2/2)$ for every real $t$; independence, measurability, endpoint order, and nonnegative scales are separate hypotheses.
--
--   Write $B(y)=\sum_i\max\{\mu_i^-y_i,\mu_i^+y_i\}$, $D(y)=\sqrt{\sum_i\sigma_i^2y_i^2}$, and $r_\varepsilon=\sqrt{2\log(1/\varepsilon)}$. The explicit safe-constraint value is $z_0+B(z)+r_\varepsilon D(z)$. The moment uncertainty set consists of all $\eta$ for which there is a vector $w$ with
--   $$\mu_i^-\le\eta_i-\sigma_iw_i\le\mu_i^+\quad\text{for all }i,\qquad \sqrt{\sum_iw_i^2}\le r_\varepsilon.$$
--   The bounded moment set intersects this set with $a_i^-\le\eta_i\le a_i^+$. The split system requires $z=u+v$, $u_0+\sum_i\max\{a_i^-u_i,a_i^+u_i\}\le0$, and $v_0+B(v)+r_\varepsilon D(v)\le0$.
--
--   The module also defines the unit-box/Euclidean-ball intersection and the lifted system $p_i+q_i=-z_i$, $\sum_i|p_i|+r\sqrt{\sum_iq_i^2}\le-z_0$ of (2.3.10). Finally, $\Phi(w)=\sum_i[\max\{\mu_i^-w_i,\mu_i^+w_i\}+\sigma_i^2w_i^2/2]$, the set of residuals admitting $\alpha>0$ with $\alpha z_0+\Phi(\alpha z)\le\log\varepsilon$, and its topological closure are distinct definitions. The closure is not defined to equal the safe-constraint sublevel set.
--
--   These concrete objects supply the shared language for the chapter's concentration and robust-representation statements.
--
--   **Formalization Note** All vectors have real coordinates; the nominal coordinate is stored separately. Scaled coordinates replace the source's extended-real quotient convention: when $\sigma_i=0$ the displacement is forced to zero. No theorem uses real division by $\sigma_i$. The radius is used with $0<\varepsilon<1$; the definitions themselves are total, with Lean's usual log and square-root conventions outside that domain. No result is assumed by a definition.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, (2.2.1)–(2.2.2), (2.3.9)–(2.3.10), P.2 and (2.4.1)–(2.4.14), printed pp. 29, 33, 45–48 (PDF pp. 55, 59, 71–74).

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RobustOpt2009.ScalarChance

/-- Residual coordinates of (2.2.1); the nominal coordinate is stored separately. -/
noncomputable def residual {L n : ℕ} (a0 : Fin n → ℝ) (b0 : ℝ)
    (a : Fin L → Fin n → ℝ) (b : Fin L → ℝ) (x : Fin n → ℝ) :
    ℝ × (Fin L → ℝ) :=
  ((∑ j, a0 j * x j) - b0, fun i => (∑ j, a i j * x j) - b i)

/-- Robust feasibility of the affine residual for every perturbation in Z. -/
def RobustFeasible {L : ℕ} (Z : Set (Fin L → ℝ)) (z : ℝ × (Fin L → ℝ)) : Prop :=
  ∀ η ∈ Z, z.1 + ∑ i, η i * z.2 i ≤ 0

/-- Strict violation probability, (2.2.2) and (2.4.5). -/
noncomputable def violation {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (z : ℝ × (Fin L → ℝ)) : ℝ :=
  P.real {ω | 0 < z.1 + ∑ i, ζ i ω * z.2 i}

/-- P.2, including finite exponential expectations so the Bochner integral is genuine.
Parameter order and nonnegative sigma are separate theorem hypotheses. -/
def MGFMajorant {L : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Measure S) (ζ : Fin L → S → ℝ) (μminus μplus σ : Fin L → ℝ) : Prop :=
  ∀ (i : Fin L) (t : ℝ),
    Integrable (fun ω => Real.exp (t * ζ i ω)) P ∧
    (∫ ω, Real.exp (t * ζ i ω) ∂P) ≤
      Real.exp (max (μminus i * t) (μplus i * t) + (σ i)^2 * t^2 / 2)

/-- The deterministic box contribution in (2.4.8), for any lower and upper endpoints. -/
noncomputable def boxTerm {L : ℕ} (lo hi y : Fin L → ℝ) : ℝ :=
  ∑ i, max (lo i * y i) (hi i * y i)

/-- The weighted Euclidean term in (2.4.8). Zero sigma is permitted. -/
noncomputable def deviation {L : ℕ} (σ y : Fin L → ℝ) : ℝ :=
  Real.sqrt (∑ i, (σ i)^2 * (y i)^2)

/-- The radius in (2.4.10) and (2.4.13); used with 0 < ε < 1. -/
noncomputable def radius (ε : ℝ) : ℝ := Real.sqrt (2 * Real.log (1 / ε))

/-- The left side of the explicit convex constraint (2.4.8). -/
noncomputable def safeValue {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z : ℝ × (Fin L → ℝ)) : ℝ :=
  z.1 + boxTerm μminus μplus z.2 + radius ε * deviation σ z.2

/-- The moment uncertainty set (2.4.10). Writing the displacement as σ_i w_i
implements the printed extended-real convention for division by zero. -/
def momentSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) : Set (Fin L → ℝ) :=
  {η | ∃ w : Fin L → ℝ,
    (∀ i, μminus i ≤ η i - σ i * w i ∧ η i - σ i * w i ≤ μplus i) ∧
    Real.sqrt (∑ i, (w i)^2) ≤ radius ε}

/-- The intersection with the known support box, (2.4.13). -/
def boundedMomentSet {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (Fin L → ℝ) :=
  {η | η ∈ momentSet μminus μplus σ ε ∧ ∀ i, alo i ≤ η i ∧ η i ≤ ahi i}

/-- The three constraints (2.4.14), including the nominal-coordinate split. -/
def SplitSystem {L : ℕ} (alo ahi μminus μplus σ : Fin L → ℝ) (ε : ℝ)
    (z u v : ℝ × (Fin L → ℝ)) : Prop :=
  z.1 = u.1 + v.1 ∧ (∀ i, z.2 i = u.2 i + v.2 i) ∧
  u.1 + boxTerm alo ahi u.2 ≤ 0 ∧ safeValue μminus μplus σ ε v ≤ 0

/-- Box intersected with a Euclidean ball, (2.3.9). -/
def boxBall {L : ℕ} (r : ℝ) : Set (Fin L → ℝ) :=
  {η | (∀ i, |η i| ≤ 1) ∧ Real.sqrt (∑ i, (η i)^2) ≤ r}

/-- The lifted conic system (2.3.10), with its printed negative residual sign. -/
def BoxBallSystem {L : ℕ} (r : ℝ) (z : ℝ × (Fin L → ℝ))
    (p q : Fin L → ℝ) : Prop :=
  (∀ i, p i + q i = -z.2 i) ∧
  (∑ i, |p i|) + r * Real.sqrt (∑ i, (q i)^2) ≤ -z.1

/-- The log-MGF upper bound Φ, (2.4.2). -/
noncomputable def phi {L : ℕ} (μminus μplus σ w : Fin L → ℝ) : ℝ :=
  ∑ i, (max (μminus i * w i) (μplus i * w i) + (σ i)^2 * (w i)^2 / 2)

/-- The exponential-certificate set Zε^o preceding (2.4.6), not a perturbation set. -/
def exponentialCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + phi μminus μplus σ (fun i => α * z.2 i) ≤ Real.log ε}

/-- The closure Zε in (2.4.6), distinct from the uncertainty set in (2.4.10). -/
def closedCertificateSet {L : ℕ} (μminus μplus σ : Fin L → ℝ) (ε : ℝ) :
    Set (ℝ × (Fin L → ℝ)) :=
  closure (exponentialCertificateSet μminus μplus σ ε)

end RobustOpt2009.ScalarChance


