-- Prove2me | Definitions.Def_PartPredAlloc_EventEC1
-- name    : PartPredAlloc_EventEC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:15.663946+00:00
-- url     : https://prove2.me/theorems/549e8e77-9009-478c-bfee-1f86e45073f3
-- title:
--   E-companion counts $R,R_1,Z,Z_1,\zeta_1$ and the local event (EC.1a)–(EC.1c)
-- statement:
--   At a time $\lambda=t/n$ with $t\in\{1,\dots,n\}$:
--
--   1. $R=|\mathcal S|$ is the size of the stochastic group and $R_1$ the number of its type-1 customers;
--   2. $Z$ is the number of positions up to time $\lambda$ that belong to $\mathcal S$;
--   3. $Z_1$ is the number of type-1 customers of the stochastic group arriving in those $Z$ positions;
--   4. $\zeta_1$ is the number of type-1 customers of the adversarial group among the first $\lambda n$ positions.
--
--   Then $O_1(\lambda)=Z_1+\zeta_1$. The local event of Appendix EC.1 is that, with $L=\log(1/\epsilon)$,
--
--   $$
--   R\in(np-\sqrt{nL},\,np+\sqrt{nL}),\quad R_1\in(n_1p-\sqrt{n_1L},\,n_1p+\sqrt{n_1L}),\quad Z\in(\lambda np-\sqrt{\lambda nL},\,\lambda np+\sqrt{\lambda nL}),
--   $$
--
--   i.e. (EC.1a)–(EC.1c) with $\alpha_{EC.2}=1$. It depends on $\mathcal S$ only and is not the event $\mathcal E$ of Definition 4.
--
--   **Formalization Note** $\lambda n=t$; the intervals are open, as printed.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, App. EC.1, pp.ec3–ec4 (PDF 40–41), Lemma EC.2 (EC.1a)–(EC.1c)

import Mathlib
import Definitions.Def_PartPredAlloc_OPT
import Definitions.Def_PartPredAlloc_expect

namespace PartPredAlloc

/-- `R`: the size of the stochastic group (arXiv:1810.00447v1, p.ec4 = PDF 41). -/
def ecR {n : ℕ} (S : Finset (Fin n)) : ℕ := S.card

/-- `R₁`: the number of type-1 customers in the stochastic group (arXiv:1810.00447v1, p.ec4). -/
def ecR1 {n : ℕ} (vI : Fin n → Cust) (S : Finset (Fin n)) : ℕ :=
  (S.filter (fun j => vI j = Cust.high)).card

/-- `Z` at `λ = t/n`: the number of positions up to time `λ` that belong to the stochastic group
(arXiv:1810.00447v1, p.ec3–ec4). -/
def ecZ {n : ℕ} (S : Finset (Fin n)) (t : ℕ) : ℕ :=
  (S.filter (fun i => i.val < t)).card

/-- `Z₁` at `λ = t/n`: the number of type-1 customers of the stochastic group that fill one of the
`Z` stochastic positions up to time `λ` (arXiv:1810.00447v1, p.ec4). -/
def ecZ1 {n : ℕ} (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  (S.filter (fun i => i.val < t ∧ arrival vI σ i = Cust.high)).card

/-- `ζ₁` at `λ = t/n`: the number of type-1 customers of the adversarial group among the first `t`
positions (arXiv:1810.00447v1, p.ec4). Adversarial customers do not move, so this is counted on
`v_I`. -/
def ecZeta1 {n : ℕ} (vI : Fin n → Cust) (S : Finset (Fin n)) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j ∉ S ∧ j.val < t ∧ vI j = Cust.high)).card

/-- The local event of Appendix EC.1 (arXiv:1810.00447v1, Lemma EC.2, p.ec4 = PDF 41, events
(EC.1a)–(EC.1c)) at `λ = t/n`, with `α_{EC.2} = 1`:
`R ∈ (np − √(n log(1/ε)), np + √(n log(1/ε)))`,
`R₁ ∈ (n₁p − √(n₁ log(1/ε)), n₁p + √(n₁ log(1/ε)))` and
`Z ∈ (λnp − √(λn log(1/ε)), λnp + √(λn log(1/ε)))`.

**Formalization Note.** `λn = t`. The intervals are open, as printed. It depends on `S` only (the
paper's footnote 11: this event is not the event `𝓔` of Definition 4). -/
def EventEC1 {n : ℕ} (p ε : ℝ) (vI : Fin n → Cust) (S : Finset (Fin n)) (t : ℕ) : Prop :=
  ((n : ℝ) * p - Real.sqrt ((n : ℝ) * Real.log (1 / ε)) < (ecR S : ℝ) ∧
    (ecR S : ℝ) < (n : ℝ) * p + Real.sqrt ((n : ℝ) * Real.log (1 / ε))) ∧
  ((nType1 vI : ℝ) * p - Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε)) < (ecR1 vI S : ℝ) ∧
    (ecR1 vI S : ℝ) < (nType1 vI : ℝ) * p + Real.sqrt ((nType1 vI : ℝ) * Real.log (1 / ε))) ∧
  ((t : ℝ) * p - Real.sqrt ((t : ℝ) * Real.log (1 / ε)) < (ecZ S t : ℝ) ∧
    (ecZ S t : ℝ) < (t : ℝ) * p + Real.sqrt ((t : ℝ) * Real.log (1 / ε)))

end PartPredAlloc


