-- Prove2me | Definitions.Def_FalconerPath_connect
-- name    : FalconerPath_connect
-- status  : Definition
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:35.697665+00:00
-- url     : https://prove2.me/theorems/7efc8118-4911-44d2-aea7-9ef87aef5ffc
-- title:
--   Cell rescaling and full-source radial heavy sets for the Falconer connection sketches
-- statement:
--   In Euclidean $\mathbb R^n$, write $h_d=2^{-d}$ and $Q(v,d,i)=\{z:v_r+i_rh_d\le z_r<v_r+(i_r+1)h_d\text{ for every }r\}$ for $i\in\mathbb Z^n$. The definition connectCellCenter gives the cell center $c_Q=(v_r+(i_r+1/2)h_d)_r$. The definition connectCellMap gives the rescaling $T_Q(z)=h_d^{-1}(z-c_Q)$. The definition connectCellLaw gives $\mu_Q=(T_Q)_\#(\rho(Q)^{-1}\rho|_Q)$, where the inverse and scalar multiplication are taken in the extended nonnegative reals, including at zero and infinity. Write $\pi_x(z)=\|z-x\|^{-1}(z-x)$ with $\pi_x(x)=0$ and $[u]_+=\max(u,0)$ as an extended nonnegative real. The definition connectRadialMass gives $M_{\rho,Q,r}(x,z)=\rho\{z'\in Q:\|\pi_x(z')-\pi_x(z)\|\le r\}$. The definition connectHeavy gives $\mathcal H_{\rho,Q,r,f}(x)=\{z\in Q\cap\operatorname{supp}\rho:[f]_+\rho(Q)<M_{\rho,Q,r}(x,z)\}$. These definitions allow every natural dimension and depth, any grid translation and index, any measure, arbitrary real $r,f$ and arbitrary points $x,z$. The comparison points $z'$ range over the entire cell without a pair-relation restriction.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, proof of Lemma 5.3 (One-scale improvement), label prep:one-scale, middle interval.

import Definitions.Def_FalconerPath_defs

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath

/-! Explicit cell geometry and full-source radial tests for the two
connection sketches (Section 5, proof of Lemma 5.3). -/
/-- Center and rescaling of the actual half-open dyadic cell. -/
def connectCellCenter {n : ℕ} (v : Space n) (d : ℕ) (i : Fin n → ℤ) : Space n :=
  WithLp.toLp 2 (fun r => v r + ((i r : ℝ)+1/2)*mesh d)

def connectCellMap {n : ℕ} (v : Space n) (d : ℕ) (i : Fin n → ℤ)
    (z : Space n) : Space n :=
  (mesh d)⁻¹ • (z-connectCellCenter v d i)

def connectCellLaw {n : ℕ} (ρ : Measure (Space n)) (v : Space n)
    (d : ℕ) (i : Fin n → ℤ) : Measure (Space n) :=
  Measure.map (connectCellMap v d i) (normalizedRestriction ρ (dyadicCell v d i))

/-- Full conditional-source test: comparison points are never restricted to G. -/
def connectRadialMass {n : ℕ} (ρ : Measure (Space n)) (Q : Set (Space n))
    (r : ℝ) (x z : Space n) : ℝ≥0∞ :=
  ρ {z' | z' ∈ Q ∧ dist (radial x z') (radial x z) ≤ r}

def connectHeavy {n : ℕ} (ρ : Measure (Space n)) (Q : Set (Space n))
    (r f : ℝ) (x : Space n) : Set (Space n) :=
  {z | z ∈ Q ∧ z ∈ ρ.support ∧ ENNReal.ofReal f * ρ Q < connectRadialMass ρ Q r x z}

end FalconerPath


