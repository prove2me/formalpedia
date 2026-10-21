-- Prove2me | Definitions.Def_CostlySeeding_EdgeQuery_Algorithm
-- name    : CostlySeeding_EdgeQuery_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:06.678865+00:00
-- url     : https://prove2.me/theorems/7a1b3a53-0133-46fa-8a05-6861b3238789
-- title:
--   Sketch estimators, parameters, stochastic SEED and Algorithm 4
-- statement:
--   For the independent cascade graph $G$, the module defines the initial-node estimator $\Gamma_\rho$, the mean of $T$ untruncated PROBE sketches $\Gamma^{(T)}_\rho$, and the corresponding threshold-$\tau$ sketch $\Gamma^{(T)}_{\rho,\tau}$. It defines the exact paper parameters
--
--   $$
--   \rho=\frac{(2+\epsilon)(\delta k\log n+\log2)}{2\epsilon^2n},\qquad
--   T=\left\lceil\frac{3(\delta+\log2)(k+1)\log n}{\epsilon^2}\right\rceil,\qquad
--   \tau=\left\lceil\frac{-n\log\epsilon}{\epsilon k}\right\rceil,
--   $$
--
--   and $E,C,Q$ of (6)–(7). SEED repeats $k$ stochastic-greedy choices on the truncated sketch; Algorithm 4 sets $\epsilon=\epsilon'/7$ and $\delta=2\log n$. Its expected spread and number of edge queries are finite weighted sums over the initial set, PROBE seeds, and SEED choices. These quantities are the two sides of Theorem 7.
--
--   **Formalization Note** The initial sample size is capped at $n$ if $\rho>1$; SEED rounds its random subset size up, caps it by the number of unselected vertices, and breaks maximizing ties by least index. All logarithms are natural.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, pp. 15–22, equations (2)–(7), Algorithms 3–4; p. 46, (30)

import Definitions.Def_CostlySeeding_EdgeQuery_Probe

namespace CostlySeeding.EdgeQuery

noncomputable def rhoPar (n k : ℕ) (eps delta : ℝ) : ℝ :=
  (2 + eps) * (delta * k * Real.log n + Real.log 2) / (2 * eps ^ 2 * n)

noncomputable def TPar (n k : ℕ) (eps delta : ℝ) : ℕ :=
  Nat.ceil (3 * (delta + Real.log 2) * (k + 1) * Real.log n / eps ^ 2)

noncomputable def tauPar (n k : ℕ) (eps : ℝ) : ℕ :=
  Nat.ceil (-(n * Real.log eps) / (eps * k))

noncomputable def EPar (n k : ℕ) (p eps : ℝ) : ℝ :=
  p * tauPar n k eps * ((tauPar n k eps : ℝ) - 1) / 2

noncomputable def CPar (n k : ℕ) (p eps delta : ℝ) : ℝ :=
  let rho := rhoPar n k eps delta
  let T := TPar n k eps delta
  n * rho * T *
    (1 + EPar n k p eps +
      Real.sqrt (delta * (tauPar n k eps * Real.log n + Real.log T) * EPar n k p eps))

noncomputable def QPar (n k : ℕ) (p eps delta : ℝ) : ℝ :=
  let T := TPar n k eps delta
  2 * CPar n k p eps delta +
    (2 + Real.sqrt 2) * T * n * Real.sqrt (delta + Real.log T)

noncomputable def GamRho {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (Vrho : Finset (Fin n)) (rho : ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 / rho) * ∑ v ∈ Vrho, phi G p v S

noncomputable def Y {n : ℕ} (Ei : Finset (Sym2 (Fin n)))
    (v : Fin n) (S : Finset (Fin n)) : ℝ :=
  if ∃ s ∈ S, (SimpleGraph.fromEdgeSet (Ei : Set (Sym2 (Fin n)))).Reachable v s then 1 else 0

noncomputable def GamCut {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (rho : ℝ) (tau : ℕ)
    (ss : Fin T → ProbeSeed n) (S : Finset (Fin n)) : ℝ :=
  (1 / rho) * ∑ v ∈ Vrho, (1 / (T : ℝ)) * ∑ i : Fin T, Y (probeCopy G Vrho tau (ss i)).1 v S

noncomputable def GamUncut {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (rho : ℝ)
    (ss : Fin T → ProbeSeed n) (S : Finset (Fin n)) : ℝ :=
  GamCut G Vrho rho (n + 1) ss S

noncomputable def queries {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (tau : ℕ) (ss : Fin T → ProbeSeed n) : ℕ :=
  ∑ i : Fin T, (probeCopy G Vrho tau (ss i)).2

noncomputable def bitW (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def seedW {n : ℕ} (p : ℝ) (s : ProbeSeed n) : ℝ :=
  let permW : ℝ := 1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  (∏ t : Fin (n + 1), permW) * (∏ v : Fin n, permW) *
    (∏ v : Fin n, ∏ w : Fin n, bitW p (s.coin v w)) *
    (∏ v : Fin n, ∏ w : Fin n, bitW p (s.redo v w))

noncomputable def initialSize (n : ℕ) (rho : ℝ) : ℕ :=
  min (Nat.ceil ((n : ℝ) * rho)) n

noncomputable def seedSampleSize (n k : ℕ) (eps : ℝ) (L : Finset (Fin n)) : ℕ :=
  min (Nat.ceil ((n : ℝ) / (k : ℝ) * Real.log (1 / eps)))
    ((Finset.univ : Finset (Fin n)) \ L).card

noncomputable def bestSeed {n : ℕ} (f : Finset (Fin n) → ℝ)
    (L R : Finset (Fin n)) : Finset (Fin n) :=
  match (R.sort (· ≤ ·)).argmax (fun v => f (insert v L) - f L) with
  | some v => insert v L
  | none => L

noncomputable def seedProb {n : ℕ} (f : Finset (Fin n) → ℝ)
    (eps : ℝ) (k : ℕ) : ℕ → Finset (Fin n) → Finset (Fin n) → ℝ
  | 0, L, A => if L = A then 1 else 0
  | j + 1, L, A =>
    let U := (Finset.univ : Finset (Fin n)) \ L
    let m := seedSampleSize n k eps L
    let choices := U.powersetCard m
    ∑ R ∈ choices, (1 / (choices.card : ℝ)) *
      seedProb f eps k j (bestSeed f L R) A

noncomputable def seedExpectation {n : ℕ} (f : Finset (Fin n) → ℝ)
    (eps : ℝ) (k : ℕ) (g : Finset (Fin n) → ℝ) : ℝ :=
  ∑ A : Finset (Fin n), seedProb f eps k k ∅ A * g A

noncomputable def initialEventProb (n m : ℕ)
    (P : Finset (Fin n) → Prop) [DecidablePred P] : ℝ :=
  let choices := (Finset.univ : Finset (Fin n)).powersetCard m
  ∑ V ∈ choices, (1 / (choices.card : ℝ)) * if P V then 1 else 0

noncomputable def seedEventProb {n T : ℕ} (p : ℝ)
    (P : (Fin T → ProbeSeed n) → Prop) [DecidablePred P] : ℝ :=
  ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
    if P ss then 1 else 0

noncomputable def probeEventProb {n T : ℕ} (p : ℝ) (m : ℕ)
    (P : Finset (Fin n) → (Fin T → ProbeSeed n) → Prop)
    [∀ V, DecidablePred (P V)] : ℝ :=
  let choices := (Finset.univ : Finset (Fin n)).powersetCard m
  ∑ V ∈ choices, (1 / (choices.card : ℝ)) *
    ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
      if P V ss then 1 else 0

noncomputable def algSpread {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (k : ℕ) (eps' : ℝ) : ℝ :=
  let eps := eps' / 7
  let delta := 2 * Real.log n
  let rho := rhoPar n k eps delta
  let T := TPar n k eps delta
  let tau := tauPar n k eps
  let choices := (Finset.univ : Finset (Fin n)).powersetCard (initialSize n rho)
  ∑ Vrho ∈ choices, (1 / (choices.card : ℝ)) *
    ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
      seedExpectation (GamCut G Vrho rho tau ss) eps k (Gam G p)

noncomputable def algQueries {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (k : ℕ) (eps' : ℝ) : ℝ :=
  let eps := eps' / 7
  let delta := 2 * Real.log n
  let rho := rhoPar n k eps delta
  let T := TPar n k eps delta
  let tau := tauPar n k eps
  let choices := (Finset.univ : Finset (Fin n)).powersetCard (initialSize n rho)
  ∑ Vrho ∈ choices, (1 / (choices.card : ℝ)) *
    ∑ ss : Fin T → ProbeSeed n, (∏ i : Fin T, seedW p (ss i)) *
      (queries G Vrho tau ss : ℝ)

end CostlySeeding.EdgeQuery


