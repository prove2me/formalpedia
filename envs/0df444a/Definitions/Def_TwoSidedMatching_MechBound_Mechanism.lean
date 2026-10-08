-- Prove2me | Definitions.Def_TwoSidedMatching_MechBound_Mechanism
-- name    : TwoSidedMatching_MechBound_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T11:04:49.005988+00:00
-- url     : https://prove2.me/theorems/bd795689-fe79-4b87-a5bc-2d911fcb9e29
-- title:
--   Main text §3–§4 and Online Appendix A.1, pp. 8–14 and OA pp. 1–3 — Poisson arrivals, problem (B), two-sided direct mechanisms, (ICd), (IRd), (ICs), (IRs)
-- statement:
--   This file sets up the two-sided market of Chen and Hu and the class of direct mechanisms of the optimal mechanism-design benchmark (B′).
--
--   **Primitives.** Buyer valuations have density $f^d$ on $[\underline v,\bar v]$ with c.d.f. $F^d$ and virtual value $V^d(v)=v-\bar F^d(v)/f^d(v)$; seller costs have density $f^s$ on $[\underline c,\bar c]$ with c.d.f. $F^s$ and virtual cost $V^s(c)=c+F^s(c)/f^s(c)$. These are the fields `loB`, `hiB`, `fB`, `cdfB`, `psiB` and `loS`, `hiS`, `fS`, `cdfS`, `psiS` of the published bilateral-trade environment.
--
--   **Arrivals.** Over $[0,T]$ buyers arrive as a Poisson process of rate $\lambda^d$ and sellers as an independent Poisson process of rate $\lambda^s$. A buyer has type $\phi=(t_\phi,v_\phi)$ (arrival time, valuation), a seller has type $\psi=(t_\psi,c_\psi)$ (arrival time, cost), and arrival times are independent of valuations and costs. The law $P$ of the arrival processes $H^T$ is encoded by the standard representation of each side: a Poisson$(\lambda T)$ number of agents and an i.i.d. sequence of types, each with arrival time uniform on $[0,T]$ and an independent valuation (cost) drawn from $F^d$ ($F^s$). The realized buyers $H^d$ and sellers $H^s$ are multisets of types. The buyer type space is $[0,T]\times[\underline v,\bar v]$ and the seller type space $[0,T]\times[\underline c,\bar c]$.
--
--   **The clairvoyant problem (B).** For buyer $\phi$ and seller $\psi$ let
--
--   $$a_{\phi\psi}=V^d(v_\phi)-V^s(c_\psi)-b\,(t_\psi-t_\phi)^+-h\,(t_\phi-t_\psi)^+ .$$
--
--   $\bar J(H^T)$ is the largest value of $\sum_{\phi,\psi}a_{\phi\psi}x_{\phi\psi}$ over $0$–$1$ matrices $x$ with every row and column sum at most one, i.e. over partial matchings of buyers to sellers; it is at least $0$ (the empty matching).
--
--   **Mechanisms.** A direct mechanism $y$ receives the reported buyer profile and the reported seller profile and assigns to every buyer type an outcome $(s_\phi,m_\phi,p_\phi)$ — discharge time, indicator that the request is honored, payment to the intermediary — and to every seller type an outcome $(s_\psi,m_\psi,p_\psi)$, the payment now going from the intermediary to the seller. It is **feasible** when, on every finite profile in the type spaces, every listed agent has $t\le s\le T$ and $m\in\{0,1\}$, and the balancing condition
--
--   $$\sum_{\phi\in H^t}\mathbf 1\{s_\phi=t,m_\phi=1\}=\sum_{\psi\in H^t}\mathbf 1\{s_\psi=t,m_\psi=1\},\qquad t\in[0,T],$$
--
--   holds. The profit is $\Pi(y^T)=\sum_{\phi\in H^T}p_\phi-\sum_{\psi\in H^T}p_\psi$. The utilities are $U^d(\phi,y)=v_\phi m-p-b(s-t_\phi)$ and $U^s(\psi,y)=p-c_\psi m-h(s-t_\psi)$, with the agent's true type and the outcome of her report.
--
--   **Interim expectations and incentive constraints.** $E_{-\phi}[g(y_{\hat\phi})]$ is the expectation, over the arrivals and types of all other agents, of $g$ at the outcome that the report $\hat\phi$ receives when it joins the buyers; for Poisson arrivals the other agents form an independent copy of $H^T$. The seller-side $E_{-\psi}$ is analogous. Then
--
--   1. (ICd): $E_{-\phi}[U^d(\phi,y_\phi)]\ge E_{-\phi}[U^d(\phi,y_{\hat\phi})]$ for all buyer types $\phi,\hat\phi$ with $t_{\hat\phi}\in[t_\phi,T]$;
--   2. (ICd′): the same for reports $\phi_{v'}=(t_\phi,v')$ only;
--   3. (IRd): $E_{-\phi}[U^d(\phi,y_\phi)]\ge 0$ for every buyer type;
--   4. (ICs), (ICs′), (IRs): the seller-side counterparts.
--
--   A mechanism is **well defined** when the outcomes are Borel functions of the listed types, the interim payments are integrable for every report in the type space, and the total absolute payments on each side are integrable.
--
--   These objects are shared by the lemmas of the mechanism-design half of Lemma 1 of the paper.
--
--   **Formalization Note.** Mechanisms may depend on the whole reported profile: the causality conditions of Online Appendix A.1 (stopping times and measurability with respect to the filtration $\mathcal H_t$) and the decision variables $\tau,a$ are dropped. This enlarges the paper's class $\mathcal Y$ (it is the clairvoyant class the paper's own proof passes to), so an upper bound proved for the larger class implies the paper's. Agents are identified by their types, as in the paper ($\phi\triangleq(t_\phi,v_\phi)$); two agents share a type only with probability zero. The reading of $E_{-\phi}$ as an expectation over an independent copy of $H^T$ is the Slivnyak–Mecke property of the Poisson process. `WellDefined` collects the measurability and integrability the paper presupposes.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 8–14, §3 and (B); Online Appendix pp. 1–3, A.1, (1), (B′)

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game
import Definitions.Def_MechanismDesign_BilateralTrade_Model
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.MechBound

open MechanismDesign.BilateralTrade

/-! ### The arrival space `H^T`

Buyers arrive on `[0, T]` as a Poisson process of rate `λ^d` with i.i.d. valuations of density
`f^d` on `[v̲, v̄] = [E.loB, E.hiB]`; sellers arrive as an independent Poisson process of rate
`λ^s` with i.i.d. costs of density `f^s` on `[c̲, c̄] = [E.loS, E.hiS]`. Each side is encoded by
its standard representation: a Poisson(`λ T`) number of agents and an i.i.d. sequence of types
`(arrival time, valuation or cost)`, the arrival time uniform on `[0, T]` and independent of the
valuation or cost. This is equal in law to the marked Poisson process restricted to `[0, T]`. -/

/-- The valuation law `F^d`: density `f^d` on `[v̲, v̄]`. -/
noncomputable def valLaw (E : Environment) : Measure ℝ :=
  (volume.restrict (Set.Icc E.loB E.hiB)).withDensity (fun v => ENNReal.ofReal (E.fB v))

/-- The cost law `F^s`: density `f^s` on `[c̲, c̄]`. -/
noncomputable def costLaw (E : Environment) : Measure ℝ :=
  (volume.restrict (Set.Icc E.loS E.hiS)).withDensity (fun c => ENNReal.ofReal (E.fS c))

/-- The law of a buyer type `φ = (t_φ, v_φ)`: arrival time and valuation independent. -/
noncomputable def buyerMark (E : Environment) (T : ℝ) : Measure (ℝ × ℝ) :=
  (TwoSidedMatching.Guarantee.timeLaw T).prod (valLaw E)

/-- The law of a seller type `ψ = (t_ψ, c_ψ)`: arrival time and cost independent. -/
noncomputable def sellerMark (E : Environment) (T : ℝ) : Measure (ℝ × ℝ) :=
  (TwoSidedMatching.Guarantee.timeLaw T).prod (costLaw E)

/-- The law `P` of the arrival processes `H^T`: buyers and sellers independent. -/
noncomputable def P (E : Environment) (lamD lamS T : ℝ) : Measure TwoSidedMatching.Guarantee.Ω :=
  (TwoSidedMatching.Guarantee.sideLaw lamD T (buyerMark E T)).prod (TwoSidedMatching.Guarantee.sideLaw lamS T (sellerMark E T))

/-- The buyers of `ω`, as the multiset of their types `φ = (t_φ, v_φ)`. -/
def Hd (ω : TwoSidedMatching.Guarantee.Ω) : Multiset (ℝ × ℝ) := (Multiset.range ω.1.1).map ω.1.2

/-- The sellers of `ω`, as the multiset of their types `ψ = (t_ψ, c_ψ)`. -/
def Hs (ω : TwoSidedMatching.Guarantee.Ω) : Multiset (ℝ × ℝ) := (Multiset.range ω.2.1).map ω.2.2

/-- The buyer type space `[0, T] × [v̲, v̄]`. -/
def buyerTypes (E : Environment) (T : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc 0 T ×ˢ Set.Icc E.loB E.hiB

/-- The seller type space `[0, T] × [c̲, c̄]`. -/
def sellerTypes (E : Environment) (T : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc 0 T ×ˢ Set.Icc E.loS E.hiS

/-! ### The clairvoyant assignment problem (B) and `J̄(H^T)` -/

/-- The coefficient of `x_{φψ}` in (B):
`V^d(v_φ) − V^s(c_ψ) − b (t_ψ − t_φ)⁺ − h (t_φ − t_ψ)⁺`. -/
noncomputable def weight (E : Environment) (b h : ℝ) (φ ψ : ℝ × ℝ) : ℝ :=
  E.psiB φ.2 - E.psiS ψ.2 - b * max (ψ.1 - φ.1) 0 - h * max (φ.1 - ψ.1) 0

/-- `J̄` of a profile: the optimal value of (B) for the buyers `D` and the sellers `S`, i.e. the
largest total weight of a partial matching (sellers as rows, buyers as columns). -/
noncomputable def JbarProfile (E : Environment) (b h : ℝ) (D S : Multiset (ℝ × ℝ)) : ℝ :=
  AssignmentGame.CoreLP.worth (M := Fin S.toList.length) (N := Fin D.toList.length)
    (fun j i => weight E b h (D.toList.get i) (S.toList.get j)) Finset.univ Finset.univ

/-- `J̄(H^T)`, the optimal value of (B) on the realized arrivals. -/
noncomputable def Jbar (E : Environment) (b h : ℝ) (ω : TwoSidedMatching.Guarantee.Ω) : ℝ :=
  JbarProfile E b h (Hd ω) (Hs ω)

/-! ### Two-sided direct mechanisms (Online Appendix A.1) -/

/-- What a mechanism assigns to one agent: the discharge time `s`, the indicator `m` that the
request is honored at `s`, and the payment `p` (paid by a buyer, received by a seller). -/
structure Outcome where
  /-- discharge time `s` -/
  s : ℝ
  /-- honored indicator `m` -/
  m : ℝ
  /-- payment `p` -/
  p : ℝ

/-- The coordinates `(s, m, p)` of an outcome. -/
def Outcome.toTriple (o : Outcome) : ℝ × ℝ × ℝ := (o.s, o.m, o.p)

/-- An anonymous direct mechanism: given the reported buyer profile and the reported seller
profile (multisets of types), it assigns an outcome to each buyer type and to each seller type.
It may use the whole reported profile (no causality restriction). -/
abbrev Mechanism :=
  Multiset (ℝ × ℝ) → Multiset (ℝ × ℝ) → (ℝ × ℝ → Outcome) × (ℝ × ℝ → Outcome)

/-- Per-agent feasibility for an agent arriving at `θ.1`: `t ≤ s ≤ T` and `m ∈ {0, 1}`. -/
def AgentFeasible (T : ℝ) (θ : ℝ × ℝ) (o : Outcome) : Prop :=
  θ.1 ≤ o.s ∧ o.s ≤ T ∧ (o.m = 0 ∨ o.m = 1)

open Classical in
/-- The demand–supply balancing condition (1): at every `t ∈ [0, T]` the number of buyers
discharged at `t` with their request honored equals the number of such sellers. -/
def Balanced (T : ℝ) (D S : Multiset (ℝ × ℝ)) (oD oS : ℝ × ℝ → Outcome) : Prop :=
  ∀ t ∈ Set.Icc 0 T,
    (D.filter (fun φ => (oD φ).s = t ∧ (oD φ).m = 1)).card =
      (S.filter (fun ψ => (oS ψ).s = t ∧ (oS ψ).m = 1)).card

/-- A feasible mechanism: on every finite profile of types in the type spaces, every listed
agent gets a feasible outcome and the balancing condition (1) holds. -/
def Feasible (E : Environment) (T : ℝ) (y : Mechanism) : Prop :=
  ∀ D S : Multiset (ℝ × ℝ), (∀ φ ∈ D, φ ∈ buyerTypes E T) → (∀ ψ ∈ S, ψ ∈ sellerTypes E T) →
    (∀ φ ∈ D, AgentFeasible T φ ((y D S).1 φ)) ∧
    (∀ ψ ∈ S, AgentFeasible T ψ ((y D S).2 ψ)) ∧
    Balanced T D S (y D S).1 (y D S).2

/-- The intermediary's profit `Π(y^T) = Σ_{φ ∈ H^T} p_φ − Σ_{ψ ∈ H^T} p_ψ` on the realized
arrivals, all agents reporting truthfully. -/
noncomputable def profit (y : Mechanism) (ω : TwoSidedMatching.Guarantee.Ω) : ℝ :=
  ((Hd ω).map (fun φ => ((y (Hd ω) (Hs ω)).1 φ).p)).sum -
    ((Hs ω).map (fun ψ => ((y (Hd ω) (Hs ω)).2 ψ).p)).sum

/-- Buyer utility `U^d(φ, y) = v_φ m − p − b (s − t_φ)`: true type `φ`, assigned outcome `o`. -/
def Ud (b : ℝ) (φ : ℝ × ℝ) (o : Outcome) : ℝ := φ.2 * o.m - o.p - b * (o.s - φ.1)

/-- Seller utility `U^s(ψ, y) = p − c_ψ m − h (s − t_ψ)`: true type `ψ`, assigned outcome `o`. -/
def Us (h : ℝ) (ψ : ℝ × ℝ) (o : Outcome) : ℝ := o.p - ψ.2 * o.m - h * (o.s - ψ.1)

/-- The interim expectation `E_{−φ}[g(y_{φ̂})]` of a buyer who reports `φ̂`: the expectation over
the other agents' arrivals and types `H^T \ {φ}` (for Poisson arrivals, an independent copy of
`H^T`), of `g` at the outcome the mechanism assigns to the report `φ̂` when `φ̂` joins the
buyers. -/
noncomputable def Eminus (E : Environment) (lamD lamS T : ℝ) (y : Mechanism) (φhat : ℝ × ℝ)
    (g : Outcome → ℝ) : ℝ :=
  ∫ ω, g ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat) ∂P E lamD lamS T

/-- The seller-side interim expectation `E_{−ψ}[g(y_{ψ̂})]` of a seller who reports `ψ̂`. -/
noncomputable def EminusS (E : Environment) (lamD lamS T : ℝ) (y : Mechanism) (ψhat : ℝ × ℝ)
    (g : Outcome → ℝ) : ℝ :=
  ∫ ω, g ((y (Hd ω) (ψhat ::ₘ Hs ω)).2 ψhat) ∂P E lamD lamS T

/-- (ICd): no buyer type `φ` gains in interim expectation by reporting a type `φ̂` in the type
space whose arrival is no earlier than her true arrival, `t_φ̂ ∈ [t_φ, T]`. -/
def ICd (E : Environment) (lamD lamS T b : ℝ) (y : Mechanism) : Prop :=
  ∀ φ ∈ buyerTypes E T, ∀ φhat ∈ buyerTypes E T, φ.1 ≤ φhat.1 →
    Eminus E lamD lamS T y φhat (Ud b φ) ≤ Eminus E lamD lamS T y φ (Ud b φ)

/-- (ICd′): the one-dimensional constraints, reports `φ_{v′} = (t_φ, v′)` with the true arrival. -/
def ICd' (E : Environment) (lamD lamS T b : ℝ) (y : Mechanism) : Prop :=
  ∀ φ ∈ buyerTypes E T, ∀ v' ∈ Set.Icc E.loB E.hiB,
    Eminus E lamD lamS T y (φ.1, v') (Ud b φ) ≤ Eminus E lamD lamS T y φ (Ud b φ)

/-- (IRd): every buyer type has nonnegative interim utility from truthful reporting. -/
def IRd (E : Environment) (lamD lamS T b : ℝ) (y : Mechanism) : Prop :=
  ∀ φ ∈ buyerTypes E T, 0 ≤ Eminus E lamD lamS T y φ (Ud b φ)

/-- (ICs): no seller type `ψ` gains by reporting `ψ̂` in the type space with `t_ψ̂ ∈ [t_ψ, T]`. -/
def ICs (E : Environment) (lamD lamS T h : ℝ) (y : Mechanism) : Prop :=
  ∀ ψ ∈ sellerTypes E T, ∀ ψhat ∈ sellerTypes E T, ψ.1 ≤ ψhat.1 →
    EminusS E lamD lamS T y ψhat (Us h ψ) ≤ EminusS E lamD lamS T y ψ (Us h ψ)

/-- (ICs′): reports `ψ_{c′} = (t_ψ, c′)` with the true arrival. -/
def ICs' (E : Environment) (lamD lamS T h : ℝ) (y : Mechanism) : Prop :=
  ∀ ψ ∈ sellerTypes E T, ∀ c' ∈ Set.Icc E.loS E.hiS,
    EminusS E lamD lamS T y (ψ.1, c') (Us h ψ) ≤ EminusS E lamD lamS T y ψ (Us h ψ)

/-- (IRs): every seller type has nonnegative interim utility from truthful reporting. -/
def IRs (E : Environment) (lamD lamS T h : ℝ) (y : Mechanism) : Prop :=
  ∀ ψ ∈ sellerTypes E T, 0 ≤ EminusS E lamD lamS T y ψ (Us h ψ)

/-- The measurability and integrability the paper leaves implicit:
1. for every number `n` of buyers and `k` of sellers, the outcome `(s, m, p)` of each listed
   agent is a Borel function of the list of types;
2. for every report in the type space, the payment of the inserted agent is integrable, so the
   interim expected payments are finite;
3. the total absolute payments on each side are integrable, so the expected profit is finite. -/
structure WellDefined (E : Environment) (lamD lamS T : ℝ) (y : Mechanism) : Prop where
  buyer_measurable : ∀ n k : ℕ, ∀ i < n,
    Measurable (fun z : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      ((y ((Multiset.range n).map z.1) ((Multiset.range k).map z.2)).1 (z.1 i)).toTriple)
  seller_measurable : ∀ n k : ℕ, ∀ j < k,
    Measurable (fun z : (ℕ → ℝ × ℝ) × (ℕ → ℝ × ℝ) =>
      ((y ((Multiset.range n).map z.1) ((Multiset.range k).map z.2)).2 (z.2 j)).toTriple)
  buyer_interim_integrable : ∀ φhat ∈ buyerTypes E T,
    Integrable (fun ω => ((y (φhat ::ₘ Hd ω) (Hs ω)).1 φhat).p) (P E lamD lamS T)
  seller_interim_integrable : ∀ ψhat ∈ sellerTypes E T,
    Integrable (fun ω => ((y (Hd ω) (ψhat ::ₘ Hs ω)).2 ψhat).p) (P E lamD lamS T)
  buyer_payments_integrable :
    Integrable (fun ω => ((Hd ω).map (fun φ => |((y (Hd ω) (Hs ω)).1 φ).p|)).sum)
      (P E lamD lamS T)
  seller_payments_integrable :
    Integrable (fun ω => ((Hs ω).map (fun ψ => |((y (Hd ω) (Hs ω)).2 ψ).p|)).sum)
      (P E lamD lamS T)

end TwoSidedMatching.MechBound


