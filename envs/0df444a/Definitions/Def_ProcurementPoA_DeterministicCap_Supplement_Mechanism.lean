-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Mechanism
-- name    : ProcurementPoA_DeterministicCap_Supplement_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:34:16.6212+00:00
-- url     : https://prove2.me/theorems/cddccc8a-9aa2-48e3-bb49-50473fb7e220
-- title:
--   Phantom mechanisms with measurable signal-dependent mixed strategies
-- statement:
--   A phantom mechanism on an arbitrary measurable signal space $\mathcal S$ consists of a probability law $\rho$ of the public signal and a Markov kernel $\kappa(s,dz)$ for the conditional phantom bid, with $\kappa(s,(R,\infty))=0$ for $\rho$-almost every $s$. It is fixed before the cost instance; costs are independent of the signal and phantom draw. The acceptance function after signal $s$ is
--   $$S_s(b)=\kappa(s,[b,\infty)).$$
--   A supplier's strategy is a Markov kernel from $(s,c)$ to real bids. Slicing at a fixed $s$ gives a published mixed profile. A mechanism equilibrium requires that this profile be a no-underbidding equilibrium for $S_s$, for almost every signal. Its cost is $\int\mathrm{SC}_s\,d\rho$, and
--   $$\operatorname{PoA}(M)=\sup_{n,D,\tau,\sigma}\frac{\int\mathrm{SC}_s\,d\rho}{\mathrm{SC}_{\mathrm{OPT}}},$$
--   where costs range over $[1,R]$, all nonempty finite populations occur, and only the mechanism's actual equilibria contribute ratios.
--
--   The mechanism is regular when, for almost every signal, $S_s$ is regular or vanishes at every bid above $1$. Define the explicit comparison function
--   $$\chi=\frac1{16},\qquad L_{\mathrm{all}}(R)=\frac{1-\chi+\sqrt{(1-\chi)^2+\chi R}}2.$$
--   These definitions keep the conditional auction separate from its signal aggregation and worst-case supremum.
--
--   **Formalization Note** Signal spaces are universe-polymorphic and need not be finite or countable. The strategy kernels require joint measurability in signal and cost. All cost expectations and PoA suprema are nonnegative extended-real operations; no equilibrium existence or lower bound is a structure field. The displayed radical is computed from $R$, independently of the actual PoA.
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Definition 5.1, §5.2, Definition 5.6 and Theorem 5.7, printed pp. 8–11 (PDF pp. 10–13)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

universe u

/-- Independent public signal and conditional phantom law, chosen before the instance.
Boundedness of the phantom is required only almost surely in the public signal. -/
structure PhantomMechanism (R : ℝ) (Sig : Type u) [MeasurableSpace Sig] where
  signalLaw : Measure Sig
  probability : IsProbabilityMeasure signalLaw
  phantom : Kernel Sig ℝ
  markov : IsMarkovKernel phantom
  bounded : ∀ᵐ s ∂signalLaw, phantom s (Set.Ioi R) = 0

instance {R : ℝ} {Sig : Type u} [MeasurableSpace Sig] (M : PhantomMechanism R Sig) :
    IsProbabilityMeasure M.signalLaw := M.probability

instance {R : ℝ} {Sig : Type u} [MeasurableSpace Sig] (M : PhantomMechanism R Sig) :
    IsMarkovKernel M.phantom := M.markov

noncomputable def signalAcceptance {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (s : Sig) (b : ℝ) : ℝ :=
  (M.phantom s (Set.Ici b)).toReal

/-- Jointly measurable randomized strategies in public signal and own cost. -/
structure MechanismProfile (Sig : Type u) [MeasurableSpace Sig] (n : ℕ) where
  bid : Suppliers n → Kernel (Sig × ℝ) ℝ
  markov : ∀ i, IsMarkovKernel (bid i)

instance {Sig : Type u} [MeasurableSpace Sig] {n : ℕ}
    (σ : MechanismProfile Sig n) (i : Suppliers n) : IsMarkovKernel (σ.bid i) := σ.markov i

noncomputable def sliceProfile {Sig : Type u} [MeasurableSpace Sig] {n : ℕ}
    (σ : MechanismProfile Sig n) (s : Sig) : MixedProfile n where
  bid i := (σ.bid i).comap (fun c : ℝ => (s, c)) (measurable_const.prodMk measurable_id)
  markov _ := inferInstance

def IsMechanismBNE {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) {n : ℕ} (D : IndependentTypes n)
    (τ : TieRule n) (σ : MechanismProfile Sig n) : Prop :=
  ∀ᵐ s ∂M.signalLaw, IsAcceptBNE D τ (sliceProfile σ s) (signalAcceptance M s)

noncomputable def mechanismSocialCost {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) {n : ℕ} (D : IndependentTypes n)
    (τ : TieRule n) (σ : MechanismProfile Sig n) : ℝ≥0∞ :=
  ∫⁻ s, acceptSocialCost D τ (sliceProfile σ s) R (signalAcceptance M s) ∂M.signalLaw

noncomputable def mechanismPoA {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) : ℝ≥0∞ :=
  sSup {q | ∃ (n : ℕ) (D : IndependentTypes n) (τ : TieRule n)
    (σ : MechanismProfile Sig n), InCostInterval D 1 R ∧ IsMechanismBNE M D τ σ ∧
      q = mechanismSocialCost M D τ σ / optimalSocialCost D}

def IsRegularMechanism {R : ℝ} {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) : Prop :=
  ∀ᵐ s ∂M.signalLaw, IsRegular R (signalAcceptance M s) ∨
    ∀ b : ℝ, 1 < b → signalAcceptance M s b = 0

noncomputable def chi : ℝ := 1 / 16

noncomputable def Lall (R : ℝ) : ℝ :=
  (1 - chi + Real.sqrt ((1 - chi) ^ 2 + chi * R)) / 2

end ProcurementPoA.DeterministicCap.Supplement


