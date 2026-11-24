-- Prove2me | Definitions.Def_SpilloverDuopoly_Switchers_Supplement_SourceThreePeriod
-- name    : SpilloverDuopoly_Switchers_Supplement_SourceThreePeriod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:38:37.048094+00:00
-- url     : https://prove2.me/theorems/da4f95a7-9a5a-4b7b-a3ad-cded99aa08e6
-- title:
--   Appendix D.2, D.4 — Gaussian learning, forward-looking consumer choices and price-selected history demand
-- statement:
--   This file realizes the four-firm, three-period consumer game rather than taking demand as an arbitrary array. Products have persistent normal values with common mean $\mu$, standard deviation $\sigma>0$ and correlation $\rho\in[0,1]$. If $Z_0,Z_1,\ldots,Z_4$ are independent standard normals, their joint law is realized by
--   $$\theta_j=\mu+\sigma\bigl(\sqrt\rho\,Z_0+\sqrt{1-\rho}\,Z_j\bigr).$$
--   After purchases $k,l$, consumers observe the corresponding coordinates; $l=0$ (outside) and $l=k$ add no distinct observation. Expected values are conditional expectations with respect to that information. Terminal utility is the maximum available expected value minus price or zero. A second-period choice maximizes current expected surplus plus $\delta$ times the conditional expected terminal option value after its trial. Thus experimentation affects current demand.
--
--   Consumer rules $a_2,a_3$ are measurable choice probabilities, sum to one including the outside option, and assign positive probability only to optimal available choices. At second-period offers $o$ and terminal offers $r$, demand is
--   $$d_2^k(o,l)=\int a_2(k,o,\theta,l)\,dP(\theta),\qquad d_3^{kl}(o,r,j)=\int a_2(k,o,\theta,l)a_3(k,o,l,r,\theta,j)\,dP(\theta).$$
--   The selected history law is $a_2(k,o,\theta,l)\,dP(\theta)$, without normalization or double weighting. Its composition changes with $o$. Terminal price deviations keep the selected factor fixed; period-2 deviations change it and their anticipated terminal prices. These integrals instantiate ThreePeriod's actual profit (30) and continuation value (31). The first-period gross value is $\mu+\delta$ times expected period-2 optimal utility, including terminal learning. Source symmetry is expressed by simultaneous firm relabelling of every price and consumer strategy, including off-path profiles; first-period tie shares remain arbitrary.
--
--   **Formalization Note** This uses the joint normal family of §2 in its symmetric four-product extension, with $\sigma$ as standard deviation. Conditional expectations are defined almost everywhere, including singular correlation endpoints. Choices depend only on observed coordinates; a consumer's own prior action adds no private information beyond those coordinates and independent tie randomization. All demand integrands are measurable and bounded on a probability space. Terminal option values and their conditional expectations are integrable since normal coordinates have finite first moments and there are finitely many finite prices. No unproved profit identity appears in the definition. The first-period outside present value $u_0$ is supplied as in the base covered-market convention.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), pp. 6–8, 49–54, 56 (PDF 8–10, 51–56, 58), §2, Appendix D.2 and D.4, eqs. (30)–(31)

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod

namespace SpilloverDuopoly.Switchers.Supplement

open MeasureTheory ProbabilityTheory Finset

/-- Persistent valuations of the four goods. No coordinate is observed before trial. -/
abbrev Values := Fin 4 → ℝ
abbrev Offers4 := Fin 4 → Offer
abbrev Choice4 := Option (Fin 4)

/-- Source primitives, §2 and Appendix D: common normal mean and standard deviation,
common nonnegative correlation, common marginal cost and discount, and the first-period
outside present value and tie rule. `rho = 0` and `rho = 1` are included. -/
structure SourceMarket where
  c : ℝ
  delta : ℝ
  mu : ℝ
  sigma : ℝ
  rho : ℝ
  u0 : ℝ
  tie : Finset (Fin 4) → Fin 4 → ℝ

namespace SourceMarket

/-- Five independent standard normal variables: one common and four product-specific shocks. -/
noncomputable def shocks : Measure (Fin 5 → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/-- Equicorrelated normal values. This realizes every common correlation in [0,1], including
perfectly identical products at rho=1, without a singular conditional-density formula. -/
noncomputable def values (M : SourceMarket) (z : Fin 5 → ℝ) : Values :=
  fun j => M.mu + M.sigma *
    (Real.sqrt M.rho * z 0 + Real.sqrt (1 - M.rho) * z j.succ)

/-- The ex-ante distribution; the affine map is continuous, hence measurable. -/
noncomputable def law (M : SourceMarket) : Measure Values :=
  Measure.map M.values shocks

/-- Information after buying k first and l second. none is the outside choice and adds
no observation; buying k again also adds no observation. -/
abbrev info (k : Fin 4) (l : Choice4) : MeasurableSpace Values :=
  MeasurableSpace.comap (fun w : Values => (w k, l.elim 0 (fun j => w j))) inferInstance

/-- Bayesian expected valuation given only the products tried, not unobserved values.
Conditional expectation avoids divisions by 1-rho or by the mass of a null history. -/
noncomputable def belief (M : SourceMarket) (k : Fin 4) (l : Choice4) (j : Fin 4) : Values → ℝ :=
  M.law[fun w => w j | info k l]

/-- Available alternatives include the outside option even if all firms withdraw. -/
def Available (o : Offers4) : Choice4 → Prop
  | none => True
  | some j => (o j).isSome

/-- Immediate expected net utility. The value assigned to an unavailable offer is immaterial:
its choice probability must be zero. The per-period outside utility is normalized to zero. -/
noncomputable def flow (M : SourceMarket) (k : Fin 4) (l : Choice4) (o : Offers4)
    (x : Choice4) (w : Values) : ℝ :=
  match x with
  | none => 0
  | some j => match o j with
    | none => 0
    | some q => M.belief k l j w - q

/-- Consumer terminal option value: the best offered net utility or the outside value zero.
The finite maximum is nonempty and bounded; unavailable products contribute only the existing
outside value zero. -/
noncomputable def terminalValue (M : SourceMarket) (k : Fin 4) (l : Choice4)
    (o : Offers4) (w : Values) : ℝ :=
  univ.sup' univ_nonempty (fun x : Choice4 => M.flow k l o x w)

/-- Continuation-price strategies are contingent on preceding period-2 offers. -/
abbrev TerminalOffers := Fin 4 → Offers4 → Choice4 → Offers4

/-- Expected two-period utility of a period-2 action, including subsequent learning and
optimal terminal consumption. The conditional expectation is BEFORE observing the new
product, whereas terminalValue uses the information AFTER that observation. -/
noncomputable def utility2 (M : SourceMarket) (o3 : TerminalOffers) (k : Fin 4)
    (o : Offers4) (x : Choice4) (w : Values) : ℝ :=
  M.flow k none o x w + M.delta *
    (M.law[M.terminalValue k x (o3 k o x) | info k none]) w

end SourceMarket

/-- Behavioral consumer tie rules, specified at every price profile. Probabilities depend
only on tried-product information. They are not free demand arrays: demand below is the
integral of these rules, and Rational requires utility maximization. Randomization only
splits utility ties. -/
structure Consumers where
  buy2 : Fin 4 → Offers4 → Values → Choice4 → ℝ
  buy3 : Fin 4 → Offers4 → Choice4 → Offers4 → Values → Choice4 → ℝ

namespace Consumers

/-- Feasible, information-respecting choice probabilities. All coordinates are bounded
between zero and one and sum to one, including the outside option. Thus all demand
integrands below are integrable under the probability law, rather than junk Bochner values. -/
def Admissible (C : Consumers) : Prop :=
  (∀ k o x, @Measurable _ _ (SourceMarket.info k none) _ (fun w => C.buy2 k o w x)) ∧
  (∀ k o l r x, @Measurable _ _ (SourceMarket.info k l) _ (fun w => C.buy3 k o l r w x)) ∧
  (∀ k o w, (∀ x, 0 ≤ C.buy2 k o w x) ∧ (∑ x, C.buy2 k o w x) = 1 ∧
    ∀ x, ¬ SourceMarket.Available o x → C.buy2 k o w x = 0) ∧
  (∀ k o l r w, (∀ x, 0 ≤ C.buy3 k o l r w x) ∧ (∑ x, C.buy3 k o l r w x) = 1 ∧
    ∀ x, ¬ SourceMarket.Available r x → C.buy3 k o l r w x = 0)

/-- Consumer sequential optimality: positive probability only on utility-maximizing
available choices. Conditions hold almost surely under the ex-ante normal law, including
counterfactual offers; they do not require a positive-mass selected segment. -/
def Rational (C : Consumers) (M : SourceMarket) (o3 : SourceMarket.TerminalOffers) : Prop :=
  C.Admissible ∧
  (∀ k o, ∀ᵐ w ∂M.law, ∀ x, 0 < C.buy2 k o w x →
    ∀ y, SourceMarket.Available o y → M.utility2 o3 k o y w ≤ M.utility2 o3 k o x w) ∧
  (∀ k o l r, ∀ᵐ w ∂M.law, ∀ x, 0 < C.buy3 k o l r w x →
    ∀ y, SourceMarket.Available r y → M.flow k l r y w ≤ M.flow k l r x w)

/-- Period-2 demand per unit of the FIRST-period share. -/
noncomputable def demand2 (C : Consumers) (M : SourceMarket) (k : Fin 4)
    (o : Offers4) (x : Choice4) : ℝ := ∫ w, C.buy2 k o w x ∂M.law

/-- Terminal demand per unit of the FIRST-period share. The factor buy2 selects the
price-dependent distribution entering history (k,l). It occurs exactly once. Terminal
price deviations change buy3 but leave the already selected factor buy2 fixed. -/
noncomputable def demand3 (C : Consumers) (M : SourceMarket) (k : Fin 4)
    (o : Offers4) (l : Choice4) (r : Offers4) (x : Choice4) : ℝ :=
  ∫ w, C.buy2 k o w l * C.buy3 k o l r w x ∂M.law

/-- Terminal distribution of values, of mass demand2 k o l. This is an UNNORMALIZED
selected measure: zero-mass histories are the zero measure, not a default probability law. -/
noncomputable def selectedLaw (C : Consumers) (M : SourceMarket) (k : Fin 4)
    (o : Offers4) (l : Choice4) : Measure Values :=
  M.law.withDensity (fun w => ENNReal.ofReal (C.buy2 k o w l))

/-- Ex-ante gross value of trying k first: first-period mean plus the discounted
period-2 Bellman value, which itself includes discounted terminal utility. -/
noncomputable def gross1 (C : Consumers) (M : SourceMarket) (o2 : Fin 4 → Offers4)
    (o3 : SourceMarket.TerminalOffers) (k : Fin 4) : ℝ :=
  M.mu + M.delta * ∫ w, ∑ x, C.buy2 k (o2 k) w x * M.utility2 o3 k (o2 k) x w ∂M.law

/-- The actual selected-history game. The lower-level pricing interface is instantiated
by consumer integrals, not by arbitrary arrays or by the desired cancellation. -/
noncomputable def game (C : Consumers) (M : SourceMarket) (o2 : Fin 4 → Offers4)
    (o3 : SourceMarket.TerminalOffers) : ThreePeriod where
  c := M.c
  delta := M.delta
  V := C.gross1 M o2 o3 0
  u0 := M.u0
  tie := M.tie
  demand2 := C.demand2 M
  demand3 := C.demand3 M

/-- Relabeling a price profile or valuation vector. -/
def relabel {α : Type} (s : Equiv.Perm (Fin 4)) (v : Fin 4 → α) : Fin 4 → α :=
  fun j => v (s.symm j)

/-- Symmetry of the consumer responses and all continuation-price strategies, including
responses AFTER ASYMMETRIC deviations. First-period tie shares remain arbitrary and are not
required to be equal. No payoff/cancellation identity is included. -/
def Symmetric (C : Consumers) (o2 : Fin 4 → Offers4)
    (o3 : SourceMarket.TerminalOffers) : Prop :=
  (∀ (s : Equiv.Perm (Fin 4)) k, o2 (s k) = relabel s (o2 k)) ∧
  (∀ (s : Equiv.Perm (Fin 4)) k o l,
    o3 (s k) (relabel s o) (l.map s) = relabel s (o3 k o l)) ∧
  (∀ (s : Equiv.Perm (Fin 4)) k o w x,
    C.buy2 (s k) (relabel s o) (relabel s w) (x.map s) = C.buy2 k o w x) ∧
  (∀ (s : Equiv.Perm (Fin 4)) k o l r w x,
    C.buy3 (s k) (relabel s o) (l.map s) (relabel s r) (relabel s w) (x.map s) =
      C.buy3 k o l r w x)

end Consumers

/-- The source parameter domain. c, delta and the tie rule use the shared first-period
Standing predicate. sigma is a STANDARD DEVIATION, as in §2, not a variance. -/
def SourceMarket.Standing (M : SourceMarket) : Prop :=
  0 < M.sigma ∧ 0 ≤ M.rho ∧ M.rho ≤ 1 ∧
  (FirstPeriod.mk M.c M.delta 0 M.u0 M.tie).Standing

end SpilloverDuopoly.Switchers.Supplement


