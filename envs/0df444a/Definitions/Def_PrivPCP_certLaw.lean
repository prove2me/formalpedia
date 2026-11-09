-- Prove2me | Definitions.Def_PrivPCP_certLaw
-- name    : PrivPCP_certLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:58.927814+00:00
-- url     : https://prove2.me/theorems/9a81f985-23b9-4b3f-b189-f8240f6e456a
-- title:
--   Nullstellensatz certificates and their uniform law
-- statement:
--   On the grid $\Omega=\prod_i S_i$ (finite sets $S_i\subseteq\mathbb F_q$), polynomials are identified with their evaluation vectors $\mathrm{ev}_\Omega(P)=(P(x))_{x\in\Omega}$.
--
--   1. $Z_a$ is the set of polynomials of individual degree at most $a$ that vanish on $D=\prod_i H_i$; we use its evaluation vectors.
--   2. The **certificates** of $g$ are the tuples $(\mathrm{ev}_\Omega Q_1,\dots,\mathrm{ev}_\Omega Q_k)$ with $Q_i\in Q_i(a)$ and $g=\mathrm{ev}_\Omega\big(\sum_i Z_iQ_i\big)$, the fibre of the map $\Phi_a$ of (23).
--   3. $\mathrm{NS}(g)$ is a uniformly random certificate of $g$.
--   4. For a law $\mu$ of $G$, the **joint law** of $(G,\mathrm{NS}(G))$ draws $G\sim\mu$ and then a uniform certificate of $G$.
--
--   These are the objects of Lemma 6.2: a random polynomial $G(m)\in Z_a$ that depends on a message $m$, together with a uniformly random Nullstellensatz certificate of it.
--
--   **Formalization Note** Under $a_i<s_i$ evaluation on $\Omega$ is injective on each $Q_i(a)$, so the uniform law on certificate evaluation tuples is the image of the uniform law on polynomial tuples. A $g$ with no certificate (never in $Z_a$, by Fact 3.3) gets the point mass at $0$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §6.2, p.36 (PDF p.38); (23), p.30 (PDF p.32); §4.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PrivPCP_gridQ

namespace PrivPCP

open Classical

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

/-- The grid `Ω = ∏_i S_i` of evaluation points, for finite sets `S_i ⊆ F` (§4.1, p.13). -/
abbrev Grid (S : Fin k → Finset F) : Type := ∀ i, ↥((S i : Finset F) : Set F)

/-- The evaluation vector `ev_Ω(P) = (P(x))_{x∈Ω}` of a polynomial on the grid `Ω = ∏_i S_i` (Bafna, Vyas,
*Private PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), §4.1, p.13). -/
noncomputable def evGrid (S : Fin k → Finset F) (P : MvPolynomial (Fin k) F) :
    Grid S → F :=
  fun x => MvPolynomial.eval (fun i => (x i : F)) P

/-- The evaluation vectors on `Ω` of `Z_a = {R ∈ P_a : R|_D = 0}`, the polynomials of individual degree at most
`a` vanishing on `D = ∏_i H_i` (§4.1, p.13). -/
def zaEval (S H : Fin k → Finset F) (a : Fin k → ℕ) : Set (Grid S → F) :=
  evGrid S '' {R | (∀ i, R.degreeOf i ≤ a i) ∧ ∀ x : Fin k → F, (∀ i, x i ∈ H i) → MvPolynomial.eval x R = 0}

/-- The certificates of `g`: the evaluation vectors `(ev_Ω Q_1, …, ev_Ω Q_k)` of the degree-bounded tuples
`Q_i ∈ Q_i(a)` with `g = ev_Ω(∑_i Z_i Q_i)` (§6.2, p.36; the map `Φ_a` of (23), p.30). -/
def certSet (S H : Fin k → Finset F) (a : Fin k → ℕ) (g : Grid S → F) :
    Set (Fin k → (Grid S → F)) :=
  {Qs | ∃ Q : Fin k → MvPolynomial (Fin k) F, (∀ i, Q i ∈ gridQ H a i) ∧ (∀ i, Qs i = evGrid S (Q i)) ∧
    g = evGrid S (∑ i, gridZ H i * Q i)}

/-- The uniform law of a certificate `NS(g) = (Q_1, …, Q_k)` of `g` (§6.2, p.36: "sample `NS(G(m))` uniformly
among the degree-bounded tuples satisfying `G(m) = ∑ Z_i Q_i`"), on evaluation vectors.

**Formalization Note** Under `a_i < s_i` evaluation on `Ω` is injective on `Q_i(a)`, so the uniform law on
evaluation tuples is the image of the uniform law on polynomial tuples. For `g` with no certificate (never the
case for `g ∈ Z_a`, by Fact 3.3) the law is the point mass at `0`. -/
noncomputable def certLaw (S H : Fin k → Finset F) (a : Fin k → ℕ) (g : Grid S → F) :
    PMF (Fin k → (Grid S → F)) :=
  if h : (certSet S H a g).toFinset.Nonempty then PMF.uniformOfFinset _ h else PMF.pure 0

/-- The joint law of `(G, NS(G))`: draw `G` from `μ`, then a uniform certificate of `G` (§6.2, p.36). -/
noncomputable def jointCertLaw (S H : Fin k → Finset F) (a : Fin k → ℕ)
    (μ : PMF (Grid S → F)) :
    PMF ((Grid S → F) × (Fin k → (Grid S → F))) :=
  μ.bind fun g => (certLaw S H a g).map fun Qs => (g, Qs)

end PrivPCP


