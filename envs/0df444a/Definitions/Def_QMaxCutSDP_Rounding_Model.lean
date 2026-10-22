-- Prove2me | Definitions.Def_QMaxCutSDP_Rounding_Model
-- name    : QMaxCutSDP_Rounding_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:47:25.904194+00:00
-- url     : https://prove2.me/theorems/8c0f4c27-cbf3-411b-894d-93fd1caaaf8a
-- title:
--   Definitions 2, 4–5 and Algorithm 1 — Quantum Max Cut, SDP (S), and rounding circuit
-- statement:
--   A weighted simple graph $G=(V,E,w)$ with $w_{ij}\ge 0$ defines the Quantum Max Cut Hamiltonian
--   $$H=\sum_{(i,j)\in E}\frac{w_{ij}}4(I-X_iX_j-Y_iY_j-Z_iZ_j).$$
--   Here $I,X,Y,Z$ are the Pauli matrices, and a Pauli string acts on one qubit at each vertex. A level-$k$ Lasserre matrix is indexed by Pauli strings of weight at most $k$, is positive semidefinite, and obeys the Pauli-product consistency constraints of Definition 4. Its objective uses $X_iX_j$, $Y_iY_j$, and $Z_iZ_j$.
--
--   The vector SDP (S) has a unit vector $v_0$, unit vectors $v_{i,a}$ and $v_{ij,a}$, and the orthogonality and product relations (1)–(8) of Definition 5. Its edge objective is $w_{ij}(v_0-v_{ij})\cdot v_0/4$, where $v_{ij}=\sum_{a=1}^3v_{ij,a}$.
--
--   Algorithm 1 chooses one of three vector families uniformly, rounds it by the signs of random projections to a bit string $z$, and applies one commuting two-qubit gate per edge. The gate angle is $\theta_{ij}=\arccos(\exp[-0.041\max(\gamma_{ij},0)])/2$, where $\gamma_{ij}=-(v_0+v_{ij})\cdot v_0/(\|v_0+v_{ij}\|\|v_0\|)$. The model defines the resulting state and its expected Hamiltonian energy.
--
--   These definitions are the shared objects used by all of the mission's theorems.
--
--   **Formalization Note** Vertices are `Fin n`, basis strings are `Fin n → Fin 2`, and each edge is counted once with $i<j$. The source's sphere-uniform vector is represented by an isotropic standard Gaussian, which gives the same signs almost surely. Ties map to zero. The gates use their equivalent cosine-sine form and a lexicographic edge order. The Lasserre objective corrects the source's duplicated $Z_iZ_j$ to $Y_iY_j$; $v_{ij,a}=v_{ji,a}$ makes the source's edge indexing explicit. The Goemans–Williamson constant uses an infimum over $[-1,1)$ to exclude the undefined quotient at $1$.
-- source:
--   Lee, Optimizing quantum circuit parameters via SDP, arXiv:2209.00789v1, p. 2, Definitions 1–2; p. 3, Definitions 3–4; pp. 5–6, Definition 5; p. 9, Algorithm 1

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open Matrix MeasureTheory ProbabilityTheory

namespace QMaxCutSDP.Rounding

abbrev SDPVector (N : ℕ) := Fin N → ℝ

/-- Definition 2, p. 2; one unweighted edge of the Quantum Max Cut Hamiltonian. -/
noncomputable def hEdge {n : ℕ} (i j : Fin n) : Operator n :=
  (1 / 4 : ℂ) • (1 - pauliString (pauliPairString 1 i j) -
    pauliString (pauliPairString 2 i j) - pauliString (pauliPairString 3 i j))

noncomputable def hamiltonian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) : Operator n :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then (w i j : ℂ) • hEdge i j else 0

noncomputable def energy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (ψ : State n) : ℝ :=
  (star ψ ⬝ᵥ (hamiltonian G w *ᵥ ψ)).re

noncomputable def lasserreEntry {n k : ℕ} (M : Matrix (PIndex n k) (PIndex n k) ℝ)
    (s t : Fin n → Fin 4) : ℝ :=
  if hs : weight s ≤ k then
    if ht : weight t ≤ k then M ⟨s, hs⟩ ⟨t, ht⟩ else 0
  else 0

/-- Definition 4, p. 3, with the duplicated Z term corrected to Y. -/
def IsLasserreFeasible (n k : ℕ) (M : Matrix (PIndex n k) (PIndex n k) ℝ) : Prop :=
  M.PosSemidef ∧
  (∀ s : PIndex n k, M s s = 1) ∧
  (∀ s t : PIndex n k,
    pauliString s.1 * pauliString t.1 + pauliString t.1 * pauliString s.1 = 0 →
      M s t = 0) ∧
  (∀ s t u v : PIndex n k,
    pauliString s.1 * pauliString t.1 = pauliString u.1 * pauliString v.1 →
      M s t = M u v) ∧
  (∀ s t u v : PIndex n k,
    pauliString s.1 * pauliString t.1 = -(pauliString u.1 * pauliString v.1) →
      M s t = -(M u v))

noncomputable def lasserreObj {n k : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Fin n → Fin n → ℝ) (_hk : 2 ≤ k)
    (M : Matrix (PIndex n k) (PIndex n k) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ G.Adj i j then
      (1 / 4 : ℝ) * w i j *
        (lasserreEntry M (fun _ => 0) (fun _ => 0) -
         lasserreEntry M (pauliPairString 1 i j) (fun _ => 0) -
         lasserreEntry M (pauliPairString 2 i j) (fun _ => 0) -
         lasserreEntry M (pauliPairString 3 i j) (fun _ => 0))
    else 0

/-- Definition 5, pp. 5–6. The array `vij` is indexed by ordered pairs; feasibility makes it symmetric. -/
structure SDPVec (n N : ℕ) where
  v0 : SDPVector N
  vi : Fin n → Fin 3 → SDPVector N
  vij : Fin n → Fin n → Fin 3 → SDPVector N

def IsSFeasible {n N : ℕ} (v : SDPVec n N) : Prop :=
  v.v0 ⬝ᵥ v.v0 = 1 ∧
  (∀ i a, v.vi i a ⬝ᵥ v.vi i a = 1) ∧
  (∀ i a b, a ≠ b → v.vi i a ⬝ᵥ v.vi i b = 0) ∧
  (∀ i j a, i ≠ j → v.vij i j a ⬝ᵥ v.vij i j a = 1) ∧
  (∀ i j a, i ≠ j → v.vi i a ⬝ᵥ v.vi j a = v.vij i j a ⬝ᵥ v.v0) ∧
  (∀ i j k a, i ≠ j → j ≠ k → i ≠ k →
    v.vij i j a ⬝ᵥ v.vij j k a = v.vij i k a ⬝ᵥ v.v0) ∧
  (∀ i j k a b, i ≠ j → j ≠ k → i ≠ k → a ≠ b →
    v.vij i j a ⬝ᵥ v.vij j k b = 0) ∧
  (∀ i j a b c, i ≠ j → a ≠ b → b ≠ c → a ≠ c →
    v.vij i j a ⬝ᵥ v.vij i j b = -(v.vij i j c ⬝ᵥ v.v0)) ∧
  (∀ i j a, i ≠ j → v.vij i j a = v.vij j i a)

def vEdge {n N : ℕ} (v : SDPVec n N) (i j : Fin n) : SDPVector N :=
  ∑ a : Fin 3, v.vij i j a

noncomputable def sObj {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → Fin n → ℝ) (v : SDPVec n N) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ G.Adj i j then
      (1 / 4 : ℝ) * w i j * ((v.v0 - vEdge v i j) ⬝ᵥ v.v0)
    else 0

/-- Algorithm 1, p. 9. -/
def alpha0 : ℝ := 0.041

noncomputable def alphaGW : ℝ :=
  sInf ((fun t : ℝ => (Real.arccos t / Real.pi) / (1 / 2 - t / 2)) '' Set.Ico (-1) 1)

noncomputable def gammaE {n N : ℕ} (v : SDPVec n N) (i j : Fin n) : ℝ :=
  -((v.v0 + vEdge v i j) ⬝ᵥ v.v0) /
    (Real.sqrt ((v.v0 + vEdge v i j) ⬝ᵥ (v.v0 + vEdge v i j)) *
      Real.sqrt (v.v0 ⬝ᵥ v.v0))

noncomputable def thetaE {n N : ℕ} (v : SDPVec n N) (i j : Fin n) : ℝ :=
  Real.arccos (Real.exp (-alpha0 * max (gammaE v i j) 0)) / 2

/-- Proof of Theorem 1, p. 12: neighbors whose edge correlation is positive. -/
noncomputable def positiveNeighbors {n N : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : SDPVec n N) (i : Fin n) : Finset (Fin n) :=
  (G.neighborFinset i).filter fun j => 0 < gammaE v i j

noncomputable def bits {n N : ℕ} (v : SDPVec n N) (a : Fin 3) (r : SDPVector N) : BitString n :=
  fun i => if 0 < v.vi i a ⬝ᵥ r then 1 else 0

def pOp {n : ℕ} (z : BitString n) (i : Fin n) : Operator n :=
  if z i = 1 then pauliAt 1 i else pauliAt 2 i

noncomputable def gate {n : ℕ} (z : BitString n) (θ : ℝ) (i j : Fin n) : Operator n :=
  (Real.cos θ : ℂ) • 1 + (Complex.I * Real.sin θ) • (pOp z i * pOp z j)

def edgeList {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => i < j ∧ G.Adj i j).map fun j => (i, j)

noncomputable def circuit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : BitString n) (θ : Fin n → Fin n → ℝ) : Operator n :=
  ((edgeList G).map fun e => gate z (θ e.1 e.2) e.1 e.2).prod

noncomputable def outState {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : BitString n) (θ : Fin n → Fin n → ℝ) : State n :=
  circuit G z θ *ᵥ Pi.single z 1

noncomputable def stdGaussian (N : ℕ) : MeasureTheory.Measure (SDPVector N) :=
  Measure.pi (fun _ : Fin N => gaussianReal 0 1)

noncomputable def expectedEnergy {n N : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Fin n → Fin n → ℝ) (v : SDPVec n N) : ℝ :=
  (1 / 3 : ℝ) * ∑ a : Fin 3,
    ∫ r, energy G w (outState G (bits v a r) (thetaE v)) ∂(stdGaussian N)

noncomputable def neighborProduct {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (θ : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∏ k ∈ (G.neighborFinset i).erase j, Real.cos (2 * θ i k)

end QMaxCutSDP.Rounding


