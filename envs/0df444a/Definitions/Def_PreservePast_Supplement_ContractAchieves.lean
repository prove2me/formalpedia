-- Prove2me | Definitions.Def_PreservePast_Supplement_ContractAchieves
-- name    : PreservePast_Supplement_ContractAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:51.060844+00:00
-- url     : https://prove2.me/theorems/3146715b-8038-449e-8e64-a5bea64a2e9a
-- title:
--   Finite success contracts: $B$-bit pre-query protocols and the fractional-subset LP value $P_e$
-- statement:
--   Let $X$ and $Y$ be nonempty finite sets of histories and queries, with nonempty legal action sets $A_q$ and a success predicate $G(x,q,a)$ such that every pair $(x,q)$ has a successful legal action.
--
--   A $B$-bit pre-query protocol **achieves error $\beta$** if its encoder writes one of $2^B$ messages from the history and the public coins, its decoder returns a legal action from the message, the coins and the query, and for every fixed pair $(x,q)$ the action is successful with probability at least $1-\beta$. $B_\beta(X,Y)$ is the least such width.
--
--   The **fractional-subset LP** minimizes $\sum_A w_A$ over nonnegative $w_A$ ($A\subseteq X$ nonempty) and $z_{A,q,a}$ subject to
--   $$\sum_{A\ni x}w_A=1\ (x\in X),\qquad \sum_a z_{A,q,a}=w_A\ (A,q),\qquad \sum_{A\ni x}\sum_a G(x,q,a)\,z_{A,q,a}\ge 1-e\ (x,q).$$
--   Its optimum is $P_e$.
--
--   **Formalization Note** Actions live in one type, possibly infinite; $z_{A,q,\cdot}$ is finitely supported on legal actions, which gives the same value as the source's LP after keeping one representative of each action's success subset. $P_e$ is the infimum of the objective over the feasible set. Measurability is required of the encoder and of the decoder's success events.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §P.1, p.72 (PDF p.74), eq. (270)

import Mathlib

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- **A B-bit pre-query protocol for a finite success contract** (the contract of `B_β(X, Y)`).
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §P.1, p.72 (PDF p.74): "Let X, Y be nonempty finite history and query sets, with nonempty
legal action sets A_q and success indicator G(x, q, a). Set G = 1 on unpromised pairs and assume
each promised pair has a successful action. Let B_β(X, Y) be the least nonnegative integer width
of a pre-query state succeeding with probability 1 − β for every fixed pair."

**Formalization Note.** Actions live in one type `Act`; `legal q` is the legal set `A_q` and
`G x q a` the success predicate. One coin space `Ω`; the encoder sees the history and the coins,
the decoder the message, the coins and the query, and always returns a legal action. Measurability
is asked of the encoder and of the success events of the decoder (`Act` carries no σ-algebra). -/
def ContractAchieves {X Y Act : Type} {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (legal : Y → Set Act) (G : X → Y → Act → Prop) (β : ℝ) (P : Measure Ω)
    (enc : X → Ω → Fin (2 ^ B)) (dec : Fin (2 ^ B) → Ω → Y → Act) : Prop :=
  IsProbabilityMeasure P ∧ (∀ x, Measurable (enc x)) ∧
    (∀ M x q, MeasurableSet {ω | G x q (dec M ω q)}) ∧ (∀ M ω q, dec M ω q ∈ legal q) ∧
    ∀ x q, ENNReal.ofReal (1 - β) ≤ P {ω | G x q (dec (enc x ω) ω q)}

/-- **Feasibility for the fractional-subset LP** (270), p.72 (PDF p.74): nonnegative `w_A`
(`A ⊆ X` nonempty) and `z_{A,q,a}` (`a` legal for `q`) with
`Σ_{A∋x} w_A = 1` for every `x`, `Σ_a z_{A,q,a} = w_A` for every `(A, q)`, and
`Σ_{A∋x} Σ_a G(x,q,a) z_{A,q,a} ≥ 1 − e` for every `(x, q)`.

**Formalization Note.** `w` is indexed by all finite subsets with `w ∅ = 0`. `z A q` is a
finitely supported function on `Act`, so the sums over actions are finite sums even when `Act`
is infinite (the cap classes of §P.2); moving the weight of an action to a representative with the
same success subset does not change the constraints or the objective, so the value is that of the
source's LP after "Retaining one representative of each action's success subset". -/
def IsLPFeasible {X Y Act : Type} [Fintype X] (legal : Y → Set Act) (G : X → Y → Act → Prop)
    (e : ℝ) (w : Finset X → ℝ) (z : Finset X → Y → Act →₀ ℝ) : Prop :=
  w ∅ = 0 ∧ (∀ A, 0 ≤ w A) ∧ (∀ A q a, 0 ≤ z A q a) ∧ (∀ A q a, z A q a ≠ 0 → a ∈ legal q) ∧
    (∀ x, ∑ A ∈ Finset.univ.filter (fun A : Finset X => x ∈ A), w A = 1) ∧
    (∀ A q, (z A q).sum (fun _ v => v) = w A) ∧
    ∀ x q, 1 - e ≤ ∑ A ∈ Finset.univ.filter (fun A : Finset X => x ∈ A),
      ((z A q).filter (fun a => G x q a)).sum (fun _ v => v)

/-- **The LP value** `P_e`: the minimum of `Σ_A w_A` over the feasible points of (270)
(§P.1, p.72: "Denote the optimum by P_e").

**Formalization Note.** A real `sInf` of the objective values. For nonempty `X`, nonempty legal
sets and a successful action for every pair the feasible set is nonempty (singleton blocks) and
the objective is `≥ 0`, so this is the infimum, attained by the compactness remark of the source. -/
noncomputable def lpValue {X Y Act : Type} [Fintype X] (legal : Y → Set Act)
    (G : X → Y → Act → Prop) (e : ℝ) : ℝ :=
  sInf {v | ∃ (w : Finset X → ℝ) (z : Finset X → Y → Act →₀ ℝ),
    IsLPFeasible legal G e w z ∧ v = ∑ A, w A}

end PreservePast.Supplement


