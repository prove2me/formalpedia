-- Prove2me | Definitions.Def_MechanismDesign_Dynamic_MultiBuyer
-- name    : MechanismDesign_Dynamic_MultiBuyer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:10:51.349409+00:00
-- url     : https://prove2.me/theorems/d85e7975-0f83-41d3-b029-b5fdffe1194b
-- title:
--   Sequential mechanism design with several buyers: interim allocation and payments, incentive compatibility, Assumption 11.2, the optimal allocation rule
-- statement:
--   This file sets up §11.2.3 (pp.224–227). There is a finite set $I$ of buyers. Buyer $i$ privately observes $\tau_i$ before contracting and her valuation $\theta_i$ after; her pair $(\tau_i,\theta_i)$ has density $g_i(\tau_i)f_i(\theta_i\mid\tau_i)$ on $[\underline\tau,\bar\tau]\times[\underline\theta,\bar\theta]$ and satisfies the single-buyer standing assumptions, and buyers are independent.
--
--   1. A **direct mechanism** is $q(\tau,\theta)=(q_1,\dots,q_N)\in\Delta$ (so $q_i\ge0$, $\sum_iq_i\le1$) and payments $t_i(\tau,\theta)$.
--   2. Buyer $i$'s interim winning probability and expected payment are
--   $$Q_i(\tau_i,\theta_i)=\mathbb E_{-i}\bigl[q_i(\tau_i,\theta_i,\tau_{-i},\theta_{-i})\bigr],\qquad T_i(\tau_i,\theta_i)=\mathbb E_{-i}\bigl[t_i(\tau_i,\theta_i,\tau_{-i},\theta_{-i})\bigr].$$
--   3. The mechanism is **incentive-compatible** (**individually rational**) if for every $i$ the single-buyer mechanism $(Q_i,T_i)$ is incentive-compatible (individually rational) in buyer $i$'s environment (Definitions 11.2, 11.3 with $q$ replaced by $Q_i$ and $t$ by $T_i$). It is **optimal** if it maximizes the expected revenue $\mathbb E[\sum_it_i]$ among incentive-compatible, individually rational mechanisms.
--   4. **Assumption 11.2**: each $\psi_i(\tau_i,\theta_i)=\theta_i+\frac{1-G_i(\tau_i)}{g_i(\tau_i)}\frac{\partial F_i(\theta_i\mid\tau_i)/\partial\tau_i}{f_i(\theta_i\mid\tau_i)}$ is increasing in $\tau_i$ and $\theta_i$.
--   5. The allocation rule of Proposition 11.11(i): $q^*_i(\tau,\theta)=1$ if $\psi_i(\tau_i,\theta_i)>0$ and $\psi_i(\tau_i,\theta_i)>\psi_j(\tau_j,\theta_j)$ for all $j\ne i$, and $0$ otherwise.
--
--   **Formalization Note** A type profile is $x:I\to\mathbb R^2$ with $x_i=(\tau_i,\theta_i)$. $Q_i$ and $T_i$ integrate over the whole profile with buyer $i$'s coordinate overwritten, which equals integrating over the other buyers' types because each buyer's law is a probability measure. Admissibility adds measurability of every $q_i$ and $t_i$, and integrability of every $t_i$ with respect to the type-profile distribution, so that the expected revenue $\mathbb E[\sum_it_i]$ is a genuine integral.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.224–227, §11.2.3, Assumption 11.2 (p.226)

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

/-!
# Sequential mechanism design with several buyers
(Krähmer & Strausz, Ch. 11 in Börgers, §11.2.3, pp.224–227)

A finite set `I` (the type `ι`) of buyers. Buyer `i` privately observes her ex ante type `τᵢ`
before contracting and her valuation `θᵢ` after; her pair `(τᵢ, θᵢ)` is distributed as in the
single-buyer model with her own `Gᵢ, gᵢ, Fᵢ, fᵢ` (the environment `E i`), on the common supports
`[τ̲, τ̄]` and `[θ̲, θ̄]`, independently across buyers.

A type profile is `x : ι → ℝ × ℝ`, `x i = (τᵢ, θᵢ)`; the book's `(τ, θ) ∈ T × Θ` is the pair of
vectors `(x · |>.1, x · |>.2)`.
-/

namespace MechanismDesign.Dynamic

open MeasureTheory

variable {τlo τhi θlo θhi : ℝ} {ι : Type*} [Fintype ι]

/-- The profile rectangle `T × Θ` with `T = [τ̲, τ̄]^N`, `Θ = [θ̲, θ̄]^N` (p.224). -/
def profileRect (ι : Type*) (τlo τhi θlo θhi : ℝ) : Set (ι → ℝ × ℝ) :=
  Set.univ.pi fun _ => typeRect τlo τhi θlo θhi

/-- The joint distribution of the type profile: buyers are independent and buyer `i`'s pair
`(τᵢ, θᵢ)` has density `gᵢ(τᵢ) fᵢ(θᵢ|τᵢ)` (pp.224–225). -/
noncomputable def profileLaw (E : ι → SeqEnv τlo τhi θlo θhi) : Measure (ι → ℝ × ℝ) :=
  (volume.restrict (profileRect ι τlo τhi θlo θhi)).withDensity
    fun x => ∏ i, ENNReal.ofReal ((E i).g (x i).1 * (E i).f (x i).2 (x i).1)

/-- A direct mechanism with several buyers (p.225): `q x i = qᵢ(τ, θ)`, the probability that
buyer `i` gets the good, and `t x i = tᵢ(τ, θ)`, buyer `i`'s payment. -/
structure MultiMechanism (ι : Type*) (τlo τhi θlo θhi : ℝ) where
  /-- `q x i = qᵢ(τ, θ)`. -/
  q : (ι → ℝ × ℝ) → ι → ℝ
  /-- `t x i = tᵢ(τ, θ)`. -/
  t : (ι → ℝ × ℝ) → ι → ℝ

namespace MultiMechanism

/-- Admissibility: on `T × Θ`, `q(τ, θ)` lies in the set `Δ` of Section 3.2.2 (`qᵢ ≥ 0` and
`∑ᵢ qᵢ ≤ 1`, p.225), every `qᵢ`, `tᵢ` is measurable, and every payment `tᵢ` is integrable
with respect to the distribution of the type profile, so that the seller's expected revenue
`E[∑ᵢ tᵢ(τ, θ)]` is defined (the measurability and integrability the book omits, Ch. 2
note 2). -/
def Admissible (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) : Prop :=
  (∀ x ∈ profileRect ι τlo τhi θlo θhi, (∀ i, 0 ≤ m.q x i) ∧ ∑ i, m.q x i ≤ 1) ∧
  ∀ i, Measurable (fun x => m.q x i) ∧ Measurable (fun x => m.t x i) ∧
    Integrable (fun x => m.t x i) (profileLaw E)

variable [DecidableEq ι]

/-- `Qᵢ(τᵢ, θᵢ)`, the expected probability that buyer `i` gets the good when her types are
`(τᵢ, θᵢ)` and the other buyers' types are drawn from their distributions (p.225). -/
noncomputable def interimQ (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) (i : ι)
    (τi θi : ℝ) : ℝ :=
  ∫ x, m.q (Function.update x i (τi, θi)) i ∂profileLaw E

/-- `Tᵢ(τᵢ, θᵢ)`, buyer `i`'s expected payment (p.225). -/
noncomputable def interimT (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) (i : ι)
    (τi θi : ℝ) : ℝ :=
  ∫ x, m.t (Function.update x i (τi, θi)) i ∂profileLaw E

/-- Buyer `i`'s interim mechanism `(Qᵢ, Tᵢ)`, a single-buyer direct mechanism. -/
noncomputable def interim (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) (i : ι) :
    DirectMechanism τlo τhi θlo θhi where
  q := m.interimQ E i
  t := m.interimT E i

/-- **Incentive compatibility** (p.225): Definition 11.2 with `q` replaced by `Qᵢ` and `t` by
`Tᵢ`, for every buyer `i`. -/
def IsIC (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) : Prop :=
  ∀ i, (m.interim E i).IsIC (E i)

/-- **Individual rationality**: Definition 11.3 for every buyer's interim mechanism. -/
def IsIR (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) : Prop :=
  ∀ i, (m.interim E i).IsIR (E i)

/-- The seller's expected revenue `E[∑ᵢ tᵢ(τ, θ)]`. -/
noncomputable def revenue (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) : ℝ :=
  ∫ x, ∑ i, m.t x i ∂profileLaw E

/-- An **optimal** mechanism: admissible, incentive-compatible, individually rational, and of
maximal expected revenue among all such mechanisms. -/
def IsOptimal (E : ι → SeqEnv τlo τhi θlo θhi) (m : MultiMechanism ι τlo τhi θlo θhi) : Prop :=
  m.Admissible E ∧ m.IsIC E ∧ m.IsIR E ∧
    ∀ m' : MultiMechanism ι τlo τhi θlo θhi, m'.Admissible E → m'.IsIC E → m'.IsIR E →
      m'.revenue E ≤ m.revenue E

end MultiMechanism

/-- **Assumption 11.2** (p.226): each buyer's virtual valuation `ψᵢ(τᵢ, θᵢ)` is increasing in
`τᵢ` and `θᵢ`. -/
def Assumption11_2 (E : ι → SeqEnv τlo τhi θlo θhi) : Prop :=
  ∀ i, (E i).Assumption11_1

/-- The optimal allocation rule of Proposition 11.11(i) (p.226):
`qᵢ(τ, θ) = 1` if `ψᵢ(τᵢ, θᵢ) > 0` and `ψᵢ(τᵢ, θᵢ) > ψⱼ(τⱼ, θⱼ)` for all `j ≠ i`, and `0`
otherwise. -/
noncomputable def optAlloc (E : ι → SeqEnv τlo τhi θlo θhi) (x : ι → ℝ × ℝ) (i : ι) : ℝ :=
  by
    classical
    exact if 0 < (E i).ψ (x i).1 (x i).2 ∧
        ∀ j, j ≠ i → (E j).ψ (x j).1 (x j).2 < (E i).ψ (x i).1 (x i).2 then 1 else 0

end MechanismDesign.Dynamic


