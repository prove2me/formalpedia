-- Prove2me | Definitions.Def_StationarityTest_Algorithm
-- name    : StationarityTest_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:18.996082+00:00
-- url     : https://prove2.me/theorems/bd4faf71-99b0-4a30-b547-f30f4720664c
-- title:
--   One round of Algorithm 3: considered neighbourhoods, estimates, minimizers and the threshold update (103)
-- statement:
--   Let $H$ be the true Hamiltonian with coefficients $h$ on $S^k_{[n]}$ and $G^{(r)}$ the current guess with coefficients $g$. A triple $(i,\Lambda,U)$ is **considered** by Algorithm 3 if $\Lambda\in CC_{i,\ell}$, the union $\Gamma_{G^{(r)}}\cup\Lambda$ is the clause set of a $(d,D,c_{gr})$ Hamiltonian, and $U\in\mathrm{Grid}(\Lambda)$. Line 3 estimates
--
--   $$\max_{P\in S^k_{[n]}}\big|\mathrm{Test}_i[P,G^{(r)}+\eta_rU;\rho_H]\big|.$$
--
--   A **round** from $g$ to $g'$ consists of the following data:
--
--   1. estimates $\hat T(i,\Lambda,U)$, each within $c_{\mathrm{meas}}\eta_r$ of this maximum for every considered triple;
--   2. for every site, a considered pair $(\Lambda_i,U_i)$ minimizing $\hat T(i,\cdot,\cdot)$;
--   3. a site assignment $P\mapsto i(P)\in\operatorname{supp}(P)$ and the update
--
--   $$g'_P=\begin{cases}g_P+\eta_r u_{i(P),P}&\text{if }|g_P+\eta_ru_{i(P),P}|\ge\tfrac14\eta_r,\\0&\text{otherwise.}\end{cases}$$
--
--   This relation is the iteration whose correctness Lemma 5.4 proves.
--
--   **Formalization Note** The round is a relation. A statement about every round therefore covers every family of estimates within tolerance, every minimizer, and every order in which the paper's loop over sites could process a clause (the last site of $\operatorname{supp}(P)$ processed determines $g'_P$). The maximum over $S^k_{[n]}$ is a supremum over a finite type. It is a maximum when $n,q,k\ge1$.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definition 5.2, (102), Algorithm 3 and (103), pp.28–29; (121), p.32

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-!
# One round of the structure learning algorithm (Algorithm 3)

T. Bergamaschi, *The stationarity test*, arXiv:2610.01074 (held file sha256 0b7e46fb…),
Definition 5.2, (102), Algorithm 3 with (103), pp.28–29; (121), p.32.

**Formalization Note.** The round is a relation, not a function: the estimates `T̂` are any
numbers within the tolerance `c_meas · η_r` of the tests they estimate, for every triple
`(i, Λ, U)` the algorithm considers; `(Λ_i, U_i)` is any minimizer of `T̂(i, ·, ·)` over those
triples; and the update (103), which Algorithm 3 performs for every site `i ∈ supp(P)` in turn
(the last one wins), is taken at an arbitrary site assignment `P ↦ i(P) ∈ supp(P)`. A statement
"for every round" therefore covers every minimizer and every processing order. The maximum over
`P ∈ S^k_[n]` of line 3 is a supremum over a finite type (a maximum when `S^k_[n]` is nonempty,
i.e. `n, q, k ≥ 1`). The guess `G^(r)` and the truth `H` are coefficient vectors on `S^k_[n]`;
`Γ_{G^(r),Λ} := Γ_{G^(r)} ∪ Λ` (p.29).
-/

variable {n q k : ℕ}

/-- Line 3 of Algorithm 3: `max_{P∈S^k_[n]} |Test_i[P, G'; ρ_H]|` for the operator `G'` and the
true Hamiltonian `H` (coefficients `h`), at inverse temperature `β`. -/
noncomputable def maxTest (β : ℝ) (h : KLocal n q k → ℝ) (i : Fin n) (G' : Op n q) : ℝ :=
  ⨆ P : KLocal n q k, ‖testSite i β P.1.mat G' (gibbs β (ham Finset.univ h))‖

/-- Line 2 of Algorithm 3: the triple `(i, Λ, U)` is considered: `Λ ∈ CC_{i,ℓ}`,
`Γ_{G^(r),Λ} = Γ_{G^(r)} ∪ Λ` is `(d, D, c_gr)` local, and `U ∈ Grid(Λ)`. -/
def Considered (ℓ d D : ℕ) (cgr κ : ℝ) (g : KLocal n q k → ℝ) (i : Fin n)
    (Λ : Finset (KLocal n q k)) (U : KLocal n q k → ℝ) : Prop :=
  IsTConnected Λ i ℓ ∧ IsDDcgr d D cgr (coeffSupport g ∪ Λ) ∧ U ∈ gridSet κ Λ

/-- Algorithm 3 with (103): `g'` is an output of one round from the guess `g = G^(r)` at accuracy
`η = η_r`, with estimates `T̂`, chosen minimizers `choice i = (Λ_i, U_i)` and update sites
`site P ∈ supp(P)`, the samples being copies of `ρ_H` for the truth `h`. -/
def IsRound3 (β : ℝ) (ℓ d D : ℕ) (cgr κ cmeas η : ℝ) (h g : KLocal n q k → ℝ)
    (T : Fin n → Finset (KLocal n q k) → (KLocal n q k → ℝ) → ℝ)
    (choice : Fin n → Finset (KLocal n q k) × (KLocal n q k → ℝ))
    (site : KLocal n q k → Fin n) (g' : KLocal n q k → ℝ) : Prop :=
  (∀ i Λ U, Considered ℓ d D cgr κ g i Λ U →
      |T i Λ U - maxTest β h i (ham Finset.univ fun P => g P + η * U P)| ≤ cmeas * η) ∧
    (∀ i, Considered ℓ d D cgr κ g i (choice i).1 (choice i).2 ∧
      ∀ Λ U, Considered ℓ d D cgr κ g i Λ U → T i (choice i).1 (choice i).2 ≤ T i Λ U) ∧
    (∀ P, site P ∈ siteSupport P.1) ∧
    ∀ P, g' P = if η / 4 ≤ |g P + η * (choice (site P)).2 P| then g P + η * (choice (site P)).2 P
      else 0

end StationarityTest


