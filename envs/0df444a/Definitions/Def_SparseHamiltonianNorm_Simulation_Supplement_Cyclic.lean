-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Cyclic
-- name    : SparseHamiltonianNorm_Simulation_Supplement_Cyclic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:29:07.143199+00:00
-- url     : https://prove2.me/theorems/f5fc6f23-cf90-4e8c-ad51-0763a3794415
-- title:
--   Full cyclic all-pass coupling and logical inclusion
-- statement:
--   Let $G,L$ be nonnegative integers, $M=G+2L$, and $\Delta=\tau/G$. Put $r=e^{-\Delta}$ and $\sigma=\sqrt{1-r^2}$. All matrices below are defined explicitly on all $M$ residues. The Fourier transform has entries $F_{kj}=M^{-1/2}e^{-2\pi i jk/M}$. Define
--   $$s(e^{i\theta})=\frac{r-e^{-i\theta}}{1-re^{-i\theta}},\qquad A^{\rm cyc}=F^\dagger\operatorname{diag}_{k}\bigl(s(e^{2\pi i k/M})\bigr)F.$$
--   The distinguished public address is $p=M-1$. Input addresses are $M-L,\ldots,M-1$, interaction addresses are $0,\ldots,G-1$, and output addresses are $G,\ldots,G+L-1$. The input vector $v_{\rm in}$ has amplitude $\sigma r^h/\sqrt{1-r^{2L}}$ at $M-1-h$; the output vector $v_{\rm out}$ has that amplitude at $G+h$, for $0\le h<L$.
--
--   For either vector $v$, let $\phi_v=(|p\rangle-v)/\sqrt{2(1-v_p)}$ and $H_v=I-2|\phi_v\rangle\langle\phi_v|$. The diagonal phases $D_+$ and $D_-$ multiply the input/output intervals by $i$ and $-i$, respectively, and fix interaction addresses. With $U_{\rm in}=D_+H_{v_{\rm in}}$ and $U_{\rm out}=D_-H_{v_{\rm out}}$, define
--   $$\widetilde w=U_{\rm out}^\dagger A^{\rm cyc}U_{\rm in}.$$
--   For a matrix $V:\mathbb C^n\to E$, its fiber extension is $\widetilde w\otimes VV^\dagger+I\otimes(I-VV^\dagger)$. The logical inclusion sends $(\xi,q)$ to $|p\rangle\otimes V\xi+\sum_{j<G}|j\rangle\otimes q_j$. This retains all completion modes. Lemma 16 supplies the nondegeneracy assumptions under which these formulas have their intended unitary meaning.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Eqs. (90)–(99), E-valued extension and logical inclusion, pp.26–28 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Supplement_Reachable

noncomputable section

namespace SparseHamiltonianNorm.Simulation.Supplement
open QAlgorithms
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Mcyc, Delta, rDelta of Eqs. (90)--(93). -/
def cyclicSize (G L : ℕ) : ℕ := G + 2 * L
def mesh (τ : ℝ) (G : ℕ) : ℝ := τ / G
def decay (τ : ℝ) (G : ℕ) : ℝ := Real.exp (-mesh τ G)

/-- The negative-exponent QFT convention in §5.1, p.26. -/
def fourier (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.of fun k j => (1 / Real.sqrt M : ℝ) *
    Complex.exp (-Complex.I * (2 * Real.pi * (j.val : ℝ) * k.val / M : ℝ))

/-- The phase sDelta(exp(i theta)) of Eq. (91). -/
def allPass (τ : ℝ) (G : ℕ) (θ : ℝ) : ℂ :=
  ((decay τ G : ℂ) - Complex.exp (-Complex.I * θ)) /
    (1 - (decay τ G : ℂ) * Complex.exp (-Complex.I * θ))

/-- Full finite cyclic filter F† D F, not its logical compression. -/
def cyclicFilter (τ : ℝ) (G L : ℕ) :
    Matrix (Fin (cyclicSize G L)) (Fin (cyclicSize G L)) ℂ :=
  let M := cyclicSize G L
  (fourier M).conjTranspose *
    Matrix.diagonal (fun k : Fin M => allPass τ G (2 * Real.pi * k.val / M)) * fourier M

/-- p=-1 mod M, safely totalized at M=0; asserted cases have L≥1. -/
def publicAddress (G L : ℕ) (j : Fin (cyclicSize G L)) : Prop :=
  j.val + 1 = cyclicSize G L

/-- The input interval consists of the last L residues; the output is [G,G+L). -/
def ioAddress (G L : ℕ) (j : Fin (cyclicSize G L)) : Prop :=
  G + L ≤ j.val ∨ (G ≤ j.val ∧ j.val < G + L)

/-- Real nonnegative vin=-i chi_in and vout=i chi_out, Eqs. (95)--(97).
Index M-1-h is -h-1; input and output signs are supplied by D± below. -/
def geometricVector (τ : ℝ) (G L : ℕ) (out : Bool) :
    Fin (cyclicSize G L) → ℂ :=
  let r := decay τ G
  let a := Real.sqrt (1 - r ^ 2) / Real.sqrt (1 - r ^ (2 * L))
  fun j =>
    if out then
      if G ≤ j.val ∧ j.val < G + L then (a * r ^ (j.val - G) : ℝ) else 0
    else
      if G + L ≤ j.val then (a * r ^ (cyclicSize G L - 1 - j.val) : ℝ) else 0

/-- Householder vector (|p>-|v>)/sqrt(2(1-vp)), Eq. (97). -/
def householderVector (τ : ℝ) (G L : ℕ) (out : Bool) :
    Fin (cyclicSize G L) → ℂ :=
  let r := decay τ G
  let vp := if out then 0 else Real.sqrt (1 - r ^ 2) / Real.sqrt (1 - r ^ (2 * L))
  fun j => ((if publicAddress G L j then 1 else 0) - geometricVector τ G L out j) /
    (Real.sqrt (2 * (1 - vp)) : ℂ)

def householder (τ : ℝ) (G L : ℕ) (out : Bool) :
    Matrix (Fin (cyclicSize G L)) (Fin (cyclicSize G L)) ℂ :=
  let v := householderVector τ G L out
  1 - (2 : ℂ) • Matrix.of (fun i j => v i * conj (v j))

/-- D+ for input and D- for output, Eq. (98). -/
def ioPhase (G L : ℕ) (out : Bool) :
    Matrix (Fin (cyclicSize G L)) (Fin (cyclicSize G L)) ℂ :=
  Matrix.diagonal fun j => if ioAddress G L j then
    (if out then -Complex.I else Complex.I) else 1

def encodingUnitary (τ : ℝ) (G L : ℕ) (out : Bool) :
    Matrix (Fin (cyclicSize G L)) (Fin (cyclicSize G L)) ℂ :=
  ioPhase G L out * householder τ G L out

/-- Eq. (99), with the entire completion modes present. -/
def cyclicCoupling (τ : ℝ) (G L : ℕ) :
    Matrix (Fin (cyclicSize G L)) (Fin (cyclicSize G L)) ℂ :=
  (encodingUnitary τ G L true).conjTranspose * cyclicFilter τ G L *
    encodingUnitary τ G L false

/-- Active-channel tensor extension plus the identity on (VH)perp, p.28. -/
def finiteCoupling {n e : ℕ} (τ : ℝ) (G L : ℕ) (V : Matrix (Fin e) (Fin n) ℂ) :
    Matrix (Fin (cyclicSize G L) × Fin e) (Fin (cyclicSize G L) × Fin e) ℂ :=
  let P := V * V.conjTranspose
  Matrix.of fun ji kh => cyclicCoupling τ G L ji.1 kh.1 * P ji.2 kh.2 +
    (if ji.1 = kh.1 then (1 - P) ji.2 kh.2 else 0)

/-- Eq. (94) with the public V embedding, on Euclidean tensor spaces. -/
def logicalInclusion {n e G L : ℕ} (V : Matrix (Fin e) (Fin n) ℂ)
    (ξ : Vec n) (q : Grid G e) : Grid (cyclicSize G L) e :=
  WithLp.toLp 2 fun ji =>
    (if publicAddress G L ji.1 then rectAction V ξ ji.2 else 0) +
    (if h : ji.1.val < G then q (⟨ji.1.val, h⟩, ji.2) else 0)

end SparseHamiltonianNorm.Simulation.Supplement


