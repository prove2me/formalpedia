-- Prove2me | Definitions.Def_TestingEstimation_Dense_CSP
-- name    : TestingEstimation_Dense_CSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:25.144389+00:00
-- url     : https://prove2.me/theorems/0a664385-dca2-43c9-a592-fc358b911060
-- title:
--   Ordered dense CSP values and the graph-derived local loss
-- statement:
--   A dense $k$-ary constraint satisfaction instance on $n$ vertices with alphabet $A$ supplies a real payoff table $P_v:A^k\to\mathbb R$ for each ordered injective tuple $v$. The predicate `PayoffsIn01` requires every table value to lie in $[0,1]$. On a vertex subset $U$ of size $m$, define the assignment score and optimum by
--
--   $$S_U(z)=m^{-k}\sum_{v\in U^k_{\ne}}P_v(z_{v_1},\ldots,z_{v_k}),\qquad \operatorname{Val}(U)=\sup_z S_U(z),\quad \operatorname{OPT}=\operatorname{Val}(V).$$
--
--   The bounded-payoff, finite nonempty alphabet, and positive-arity conditions are explicit in the sampling theorem. It also asserts attainment. Restriction retains the same payoff tables; there is no symmetry requirement on them. The expected sampled optimum is the uniform average of $\operatorname{Val}(U)$ over $m$-subsets.
--
--   For the graph construction, $s=a+2$, the alphabet is $\Lambda$, and for an ordered injective sample $v$ and tuple of labels $\zeta$, set $Y(ab)=D(G(v_av_b),\zeta_a,\zeta_b)$ and
--
--   $$\ell_v(\zeta)=\binom s2^{-1}\sum_{ab}\bigl[G(v_av_b)(1-Y(ab))+(1-G(v_av_b))Y(ab)\bigr]+2\phi(Y).$$
--
--   The derived instance $I(G)$ has payoff $P_v=1-\ell_v/3$. The loss and payoff bounds are theorem obligations in Lemma 5. Define $a_n=(n)_s/n^s$, using the falling factorial, to account for collisions in independently sampled tuples. The denominator of every CSP score is $m^k$, rather than $(m)_k$. In all restrictions the original rejection rule, decoder, label alphabet, and parameters stay fixed. This layer provides the actual optimization problem; it supplies no assertion that sample optima approximate its full optimum.
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), §4.3, pp. 15–16 (PDF pages equal printed pages)

import Definitions.Def_TestingEstimation_Dense_Labels

noncomputable section

namespace TestingEstimation.Dense
attribute [local instance] Classical.propDecidable

/-- An ordered-tuple CSP table; the payoff bound is imposed explicitly by its theorems. -/
structure DenseCSP (n k : ℕ) (A : Type) where
  payoff : (Fin k ↪ Fin n) → (Fin k → A) → ℝ

def PayoffsIn01 {n k : ℕ} {A : Type} (I : DenseCSP n k A) : Prop :=
  ∀ v ζ, 0 ≤ I.payoff v ζ ∧ I.payoff v ζ ≤ 1

def cspScore {n k : ℕ} {A : Type} (I : DenseCSP n k A) (U : Finset (Fin n))
    (z : {v // v ∈ U} → A) : ℝ :=
  (∑ v : Fin k ↪ {u // u ∈ U},
    I.payoff (v.trans ⟨Subtype.val, Subtype.val_injective⟩) (fun i => z (v i))) /
    (U.card : ℝ)^k

def cspValue {n k : ℕ} {A : Type} (I : DenseCSP n k A) (U : Finset (Fin n)) : ℝ :=
  sSup (Set.range (cspScore I U))

def optimum {n k : ℕ} {A : Type} (I : DenseCSP n k A) : ℝ := cspValue I Finset.univ

def sampleValue {n k : ℕ} {A : Type} (I : DenseCSP n k A) (m : ℕ) : ℝ :=
  mean (fun U : {U : Finset (Fin n) // U.card = m} => cspValue I U.val)

/-- The same original rule and decoder are retained in every sampled constraint. -/
def tupleDecoded {a n : ℕ} (f : Rule (a+2)) (γ : ℝ) (G : Graph n)
    (v : Fin (a+2) ↪ Fin n) (ζ : Fin (a+2) → Label a γ) : WGraph (a+2) :=
  fun e => decoder f γ (G (mapEdge v e)) (ζ e.val.1) (ζ e.val.2)

def tupleLoss {a n : ℕ} (f : Rule (a+2)) (γ : ℝ) (G : Graph n)
    (v : Fin (a+2) ↪ Fin n) (ζ : Fin (a+2) → Label a γ) : ℝ :=
  let Y := tupleDecoded f γ G v ζ
  mean (fun e => bit (G (mapEdge v e)) * (1 - (Y e : ℝ)) +
    (1 - bit (G (mapEdge v e))) * (Y e : ℝ)) + 2 * phi f Y

def graphInstance {a n : ℕ} (f : Rule (a+2)) (γ : ℝ) (G : Graph n) :
    DenseCSP n (a+2) (Label a γ) where
  payoff v ζ := 1 - tupleLoss f γ G v ζ / 3

def collisionFactor (n s : ℕ) : ℝ := (n.descFactorial s : ℝ) / (n : ℝ)^s

end TestingEstimation.Dense


