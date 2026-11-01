-- Prove2me | Definitions.Def_PartPredAlloc_obsCount
-- name    : PartPredAlloc_obsCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:17.69299+00:00
-- url     : https://prove2.me/theorems/b9faba28-19df-4519-9156-fa6fcb4843ee
-- title:
--   Observed counts $O_j(\lambda)$, $O^{\mathcal S}_2(\lambda)$, $\eta_j(\lambda)$ and approximations $\tilde o_j(\lambda)$, $\tilde o^{\mathcal S}_2(\lambda)$
-- statement:
--   Time is normalized: $\lambda\in\{0,1/n,\dots,1\}$, and "up to time $\lambda$" means the slots $1,\dots,\lambda n$. For the outcome $(\mathcal S,\sigma)$ and $j=1,2$:
--
--   1. $O_j(\lambda)$ is the number of type-$j$ customers arriving up to time $\lambda$ in $\vec V$;
--   2. $O^{\mathcal S}_2(\lambda)$ is the number of type-2 customers of the stochastic group arriving up to time $\lambda$;
--   3. $\eta_j(\lambda)$ is the number of type-$j$ customers among the first $\lambda n$ customers of $\vec v_I$ (deterministic);
--   4. the deterministic approximations are
--   $$
--   \tilde o_j(\lambda)=(1-p)\eta_j(\lambda)+p\lambda n_j,\qquad \tilde o^{\mathcal S}_2(\lambda)=p\lambda n_2 .
--   $$
--
--   Lemma 1 shows that the observed counts stay close to these approximations.
--
--   **Formalization Note** $\lambda=t/n$ with $t\in\{0,\dots,n\}$; slot $t$ is `i : Fin n` with `i.val + 1 = t`. A slot holds a stochastic-group customer iff it lies in $\mathcal S$, since $\sigma$ maps $\mathcal S$ onto itself, so $O^{\mathcal S}_2$ counts slots in $\mathcal S$.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, §3.1, p.11, Table 1 (p.12)

import Mathlib
import Definitions.Def_PartPredAlloc_OPT
import Definitions.Def_PartPredAlloc_expect

namespace PartPredAlloc

/-- The number of periods among the first `t` (slots `1, …, t`, i.e. the `i : Fin n` with
`i.val < t`) at which the sequence `v` has value `c`. -/
def obsCount {n : ℕ} (c : Cust) (v : Fin n → Cust) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i.val < t ∧ v i = c)).card

/-- `O₁(λ)` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11): the number of type-1 customers arriving
up to time `λ` in the arrival sequence `v_I ∘ σ⁻¹`. -/
def O1 {n : ℕ} (vI : Fin n → Cust) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  obsCount Cust.high (arrival vI σ) t

/-- `O₂(λ)` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11): the number of type-2 customers arriving
up to time `λ`. -/
def O2 {n : ℕ} (vI : Fin n → Cust) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  obsCount Cust.low (arrival vI σ) t

/-- `O^S₂(λ)` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11): the number of type-2 customers of the
stochastic group `S` arriving up to time `λ`.

**Formalization Note.** A slot holds a stochastic-group customer iff the slot lies in `S`, because
`σ` maps `S` onto `S`; the count is therefore over slots `i ∈ S`. -/
def OS2 {n : ℕ} (vI : Fin n → Cust) (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i.val < t ∧ i ∈ S ∧ arrival vI σ i = Cust.low)).card

/-- `η₁(λ)` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11): the number of type-1 customers among the
first `λn = t` customers of the adversarial sequence `v_I`. -/
def eta1 {n : ℕ} (vI : Fin n → Cust) (t : ℕ) : ℕ :=
  obsCount Cust.high vI t

/-- `η₂(λ)` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11): the number of type-2 customers among the
first `t` customers of `v_I`. -/
def eta2 {n : ℕ} (vI : Fin n → Cust) (t : ℕ) : ℕ :=
  obsCount Cust.low vI t

/-- `õ₁(λ) = (1 − p) η₁(λ) + p λ n₁` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11). -/
noncomputable def otilde1 {n : ℕ} (p : ℝ) (vI : Fin n → Cust) (t : ℕ) : ℝ :=
  (1 - p) * eta1 vI t + p * ((t : ℝ) / n) * nType1 vI

/-- `õ₂(λ) = (1 − p) η₂(λ) + p λ n₂` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11). -/
noncomputable def otilde2 {n : ℕ} (p : ℝ) (vI : Fin n → Cust) (t : ℕ) : ℝ :=
  (1 - p) * eta2 vI t + p * ((t : ℝ) / n) * nType2 vI

/-- `õ^S₂(λ) = p λ n₂` at `λ = t/n` (arXiv:1810.00447v1, §3.1, p.11). -/
noncomputable def otildeS2 {n : ℕ} (p : ℝ) (vI : Fin n → Cust) (t : ℕ) : ℝ :=
  p * ((t : ℝ) / n) * nType2 vI

end PartPredAlloc


