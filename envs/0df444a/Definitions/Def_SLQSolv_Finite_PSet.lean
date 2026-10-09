-- Prove2me | Definitions.Def_SLQSolv_Finite_PSet
-- name    : SLQSolv_Finite_PSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:31.221954+00:00
-- url     : https://prove2.me/theorems/e39b08d2-f160-418e-8e18-15fc9970f7d3
-- title:
--   Λ(s, P(·)) and 𝒫[t, T], p. 2292 — absolutely continuous P with P(T) ⩽ G and Λ(s, P) ⩾ 0
-- statement:
--   For an absolutely continuous function $P:[t,T]\to\mathbb S^n$ define the $(n+m)\times(n+m)$ block matrix
--
--   $$
--   \Lambda(s,P(\cdot))=\begin{pmatrix}\dot P+PA+A^\top P+C^\top PC+Q & PB+C^\top PD+S^\top\\ B^\top P+D^\top PC+S & R+D^\top PD\end{pmatrix}(s),
--   $$
--
--   and let
--
--   $$
--   \mathcal P[t,T]=\Big\{P\in AC(t,T;\mathbb S^n)\ \Big|\ P(T)\le G,\ \Lambda(s,P(\cdot))\ge0\ \text{a.e. }s\in[t,T]\Big\}.
--   $$
--
--   A nonempty $\mathcal P[t,T]$ is a sufficient condition for Problem (SLQ)$^0$ to be finite at $t$ (Proposition 5.1, (v) ⇒ (ii)), and the sufficient condition of Corollary 5.4 is proved by exhibiting an element of $\mathcal P[0,T]$.
--
--   **Formalization Note** Absolute continuity is encoded by a witness `Pdot` for the derivative: $P(r)=P(T)-\int_r^T\dot P(s)\,ds$ for $r\in[t,T]$ with $\dot P\in L^1(t,T)$ entrywise. $P(s)$ is symmetric for $s\in[t,T]$. Matrix inequalities are in the Loewner order (`PosSemidef` of the difference). The block matrix is indexed by `Fin n ⊕ Fin m` through `Matrix.fromBlocks`.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §5, definitions of Λ(s, P(·)) and 𝒫[t, T], p. 2292

import Mathlib
import Definitions.Def_SLQSolv_Finite_Setting

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

variable {Ω : Type*} {n m : ℕ}

/-- The block matrix `Λ(s, P(·))` of p. 2292, for `P` with derivative `Ṗ = Pdot`:
`Λ = [[Ṗ + PA + AᵀP + CᵀPC + Q, PB + CᵀPD + Sᵀ], [BᵀP + DᵀPC + S, R + DᵀPD]]`, an
`(n + m) × (n + m)` matrix indexed by `Fin n ⊕ Fin m`. -/
def lambdaMat (d : Data Ω n m) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.fromBlocks
    (Pdot s + P s * d.A s + (d.A s)ᵀ * P s + (d.C s)ᵀ * P s * d.C s + d.Q s)
    (P s * d.B s + (d.C s)ᵀ * P s * d.D s + (d.S s)ᵀ)
    ((d.B s)ᵀ * P s + (d.D s)ᵀ * P s * d.C s + d.S s)
    (d.R s + (d.D s)ᵀ * P s * d.D s)

/-- `P ∈ 𝒫[t, T]` (p. 2292), witnessed by its derivative `Pdot`: `P : [t, T] → 𝕊ⁿ` is absolutely
continuous, written `P(r) = P(T) − ∫ᵣᵀ Pdot(s) ds` for `r ∈ [t, T]` with `Pdot ∈ L¹(t, T)`;
`P(T) ⩽ G`; and `Λ(s, P(·)) ⩾ 0` for a.e. `s ∈ [t, T]`. -/
structure IsInPSet (d : Data Ω n m) (t : ℝ≥0) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) :
    Prop where
  symm : ∀ s, t ≤ s → s ≤ d.T → (P s).IsSymm
  integrable : ∀ i j, IntegrableOn (fun s : ℝ => Pdot s.toNNReal i j) (Icc (t : ℝ) d.T)
  absCont : ∀ r, t ≤ r → r ≤ d.T → ∀ i j,
    P r i j = P d.T i j - ∫ s in Icc (r : ℝ) d.T, Pdot s.toNNReal i j
  terminal : (d.G - P d.T).PosSemidef
  lambda_nonneg : ∀ᵐ s ∂(volume.restrict (Icc (t : ℝ) d.T)),
    (lambdaMat d P Pdot s.toNNReal).PosSemidef

end SLQSolv.Finite


