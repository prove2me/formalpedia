-- Prove2me | Definitions.Def_RobustOpt2009_Bernstein_Setup
-- name    : RobustOpt2009_Bernstein_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:45.190785+00:00
-- url     : https://prove2.me/theorems/50598783-1bf3-4ac2-b359-bf880ce2a6c7
-- title:
--   Bernstein approximation: chance constraints, perspectives, and affine conjugate data
-- statement:
--   Let $\mathbb R^n$ have its usual finite-dimensional topology and pairing $\langle x,y\rangle=\sum_i x_i y_i$. The affine conjugate data consist of a finite real-valued function $\Phi:\mathbb R^L\to\mathbb R$, a function $\phi:\mathbb R^M\to\overline{\mathbb R}$, a linear map $A$, and a translation $a$. Write $U_c=\{u:\phi(u)\le c\}$ and impose the representation
--   $$\Phi(w)=\sup_u\{\langle w,Au+a\rangle-\phi(u)\}.$$
--   For a probability distribution $P$, Q.1 requires convexity of $\Phi$, $\Phi(0)=0$, and $\int e^{\langle w,\zeta\rangle}\,dP\le e^{\Phi(w)}$ for every $w$. Q.2 excludes $-\infty$ values of $\phi$, requires its real epigraph to be convex and all real sublevel sets closed and bounded, and requires the displayed representation.
--
--   For $0<\epsilon<1$, define
--   $$Z^o_\epsilon=\{(z_0,w):\exists\alpha>0,\ \alpha z_0+\Phi(\alpha w)\le\log\epsilon\},\quad Z_\epsilon=\operatorname{cl}Z^o_\epsilon,$$
--   $$V_\epsilon(z_0,w)=\inf_{\beta>0}[z_0+\beta\Phi(\beta^{-1}w)+\beta\log(1/\epsilon)],\quad \mathcal Z_\epsilon=A U_{\log(1/\epsilon)}+a.$$
--   The chance-feasible set is $\{(z_0,w):P(z_0+\langle w,\zeta\rangle>0)\le\epsilon\}$. A set is normal safe when it is a subset of that set, closed and convex, contains zero, is closed under nonnegative scaling, contains $(-1,0)$ in its interior, and excludes $(1,0)$, as in Remark 4.1.2.
--
--   The appendix constructions are $H^o=\{z:\exists\beta>0,H(\beta^{-1}z)\le a\}$, $G(z)=\inf_{\beta>0}[\beta H(\beta^{-1}z)-\beta a]$, and $Z^\rho=\operatorname{cl}\{z:\exists\alpha>0,\Psi(\alpha z)\le\rho\}$. These definitions separate the probability model, coefficient sets, and perturbation sets used by the mission.
--
--   **Formalization Note** Coordinates use `Fin n`; coefficients are pairs $(z_0,w)$. Infima and suprema are computed in `EReal`, and all perspective scales are strictly positive. The MGF uses a nonnegative extended integral, equivalent to the logarithmic bound under the probability and finiteness assumptions. The raw data structure allows both infinities; Q.2 and the appendix hypotheses explicitly exclude $-\infty$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Definition 4.1.1, Remark 4.1.2, Q.1–2, (4.2.5)–(4.2.7), (4.2.11), printed pp. 81–86 (PDF pp. 107–112); Lemma B.1.1 and Theorem B.1.2, printed pp. 471, 473 (PDF pp. 497, 499)

import Mathlib

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RobustOpt2009.Bernstein

/-- Coordinate spaces, with their standard finite-dimensional topology. -/
abbrev Space (n : ℕ) := Fin n → ℝ

/-- Data of the affine conjugate representation (4.2.7). -/
structure Setup (L M : ℕ) where
  Phi : Space L → ℝ
  phi : Space M → EReal
  A : Space M →ₗ[ℝ] Space L
  a : Space L

/-- The ordinary coordinate pairing. -/
def pairing {n : ℕ} (x y : Space n) : ℝ := ∑ i, x i * y i

/-- Real sublevel sets, retaining the extended-real value of the function. -/
def sublevel {n : ℕ} (f : Space n → EReal) (c : ℝ) : Set (Space n) :=
  {x | f x ≤ (c : EReal)}

/-- The affine conjugate supremum in (4.2.7). -/
def representation {n m : ℕ} (F : Space n → ℝ) (f : Space m → EReal)
    (A : Space m →ₗ[ℝ] Space n) (a : Space n) : Prop :=
  ∀ w, (F w : EReal) = ⨆ u, (pairing w (A u + a) : EReal) - f u

/-- Q.1 in its equivalent exponential form; the nonnegative integral cannot
return a spurious zero on nonintegrable exponentials. -/
def Q1 {L : ℕ} (P : Measure (Space L)) (Phi : Space L → ℝ) : Prop :=
  ConvexOn ℝ univ Phi ∧ Phi 0 = 0 ∧
  ∀ w, (∫⁻ ζ, ENNReal.ofReal (Real.exp (pairing w ζ)) ∂P) ≤
    ENNReal.ofReal (Real.exp (Phi w))

/-- Q.2: extended-real convexity is convexity of the real epigraph;
lower semicontinuity is closedness of every real sublevel set. -/
def Q2 {L M : ℕ} (d : Setup L M) : Prop :=
  (∀ u, d.phi u ≠ ⊥) ∧
  Convex ℝ {p : Space M × ℝ | d.phi p.1 ≤ (p.2 : EReal)} ∧
  (∀ c, IsClosed (sublevel d.phi c)) ∧
  (∀ c, Bornology.IsBounded (sublevel d.phi c)) ∧
  representation d.Phi d.phi d.A d.a

/-- The coefficient set before closure, equation (4.2.5). -/
def initialSet {L : ℕ} (Phi : Space L → ℝ) (ε : ℝ) : Set (ℝ × Space L) :=
  {z | ∃ α : ℝ, 0 < α ∧ α * z.1 + Phi (α • z.2) ≤ Real.log ε}

/-- The closed Bernstein coefficient-feasibility set, equation (4.2.5). -/
def feasibleSet {L : ℕ} (Phi : Space L → ℝ) (ε : ℝ) : Set (ℝ × Space L) :=
  closure (initialSet Phi ε)

/-- The left side of (4.2.6), with the infimum computed in the complete lattice EReal. -/
def bernsteinValue {L : ℕ} (Phi : Space L → ℝ) (ε : ℝ) (z : ℝ × Space L) : EReal :=
  ⨅ β : {b : ℝ // 0 < b},
    ((z.1 + β.val * Phi (β.val⁻¹ • z.2) + β.val * Real.log (1 / ε) : ℝ) : EReal)

/-- The actual chance-feasible set (4.0.1), with a strict violation event. -/
def chanceSet {L : ℕ} (P : Measure (Space L)) (ε : ℝ) : Set (ℝ × Space L) :=
  {z | P {ζ | 0 < z.1 + pairing z.2 ζ} ≤ ENNReal.ofReal ε}

/-- Normal safe approximation in the equivalent form of Remark 4.1.2. -/
def normalSafe {L : ℕ} (P : Measure (Space L)) (ε : ℝ)
    (S : Set (ℝ × Space L)) : Prop :=
  S ⊆ chanceSet P ε ∧ IsClosed S ∧ Convex ℝ S ∧ (0 : ℝ × Space L) ∈ S ∧
  (∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t • z ∈ S) ∧
  ((-1, 0) : ℝ × Space L) ∈ interior S ∧ ((1, 0) : ℝ × Space L) ∉ S

/-- The perturbation set in (4.2.11), separate from the coefficient set. -/
def uncertaintySet {L M : ℕ} (d : Setup L M) (ε : ℝ) : Set (Space L) :=
  (fun u => d.A u + d.a) '' sublevel d.phi (Real.log (1 / ε))

/-- Homogenized sublevel cone before closure, Lemma B.1.1. -/
def initialCone {n : ℕ} (H : Space n → EReal) (a : ℝ) : Set (Space n) :=
  {z | ∃ β : ℝ, 0 < β ∧ H (β⁻¹ • z) ≤ (a : EReal)}

/-- Perspective infimum in Lemma B.1.1; only positive scalars multiply H. -/
def perspectiveValue {n : ℕ} (H : Space n → EReal) (a : ℝ) (z : Space n) : EReal :=
  ⨅ β : {b : ℝ // 0 < b},
    (β.val : EReal) * H (β.val⁻¹ • z) - ((β.val * a : ℝ) : EReal)

/-- The closed homogenized sublevel set of Theorem B.1.2. -/
def dualCone {n : ℕ} (Psi : Space n → ℝ) (ρ : ℝ) : Set (Space n) :=
  closure {z | ∃ α : ℝ, 0 < α ∧ Psi (α • z) ≤ ρ}

end RobustOpt2009.Bernstein


