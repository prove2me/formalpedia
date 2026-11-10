-- Prove2me | Definitions.Def_SYKFastMix_FastMixing_Model
-- name    : SYKFastMix_FastMixing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:26.823148+00:00
-- url     : https://prove2.me/theorems/60fccdd8-44ae-4690-afeb-64e7b42cce72
-- title:
--   SYK disorder, arbitrary Majoranas, parity, and block operators
-- statement:
--   Let $N\ge4$ be even, $J>0$, and $d=2^{N/2}$. Choose any Hermitian Majorana family on $\mathbb C^d$ satisfying $\{\gamma_i,\gamma_j\}=2\delta_{ij}I$. For each four-element set $A$, let $\gamma_A$ be its ordered product, without a complex phase. The disorder space and its probability law are
--   $$\Omega=\mathbb R^{\binom{[N]}4},\qquad \mathbb P_J=\bigotimes_{|A|=4}\mathcal N(0,6J^2/N^3),\qquad H(w)=\sum_{|A|=4}w_A\gamma_A.$$
--   Define $\gamma_i(s)=e^{-sH}\gamma_i e^{sH}$, $P_f=\mathrm i^{N/2}\gamma_1\cdots\gamma_N$, $P(X)=P_fXP_f$, and $\partial_iX=(\gamma_iX-P(X)\gamma_i)/2$. Put $\widetilde\gamma_i=\gamma_i(\beta/4)$, $c_i(X)=(\widetilde\gamma_iX-X\widetilde\gamma_i^\dagger)/2$, $c_i^f(X)=(A_iX-XA_i^\dagger)/2$, and $b_i(X)=(\widetilde\gamma_iX-P(X)\widetilde\gamma_i^\dagger)/2$. The positive operators are $K=\sum_i c_i^\dagger c_i$ and $K_f=\sum_i(c_i^f)^\dagger c_i^f$.
--
--   The Jacobian has blocks $(D\gamma(s))_{ji}=\{\gamma_i,\gamma_j(s)\}/2$. With the antisymmetric extension of $w_A$ to ordered tuples, define
--   $$M(A,B)_{ij}(X)=\tfrac13\sum_{k,l}w_{ijkl}(A_kA_lX-A_kXB_l+XB_kB_l).$$
--   This supplies the source model for every quantum milestone. **Formalization Note** Sites use $0,\ldots,N-1$; matrix and superoperator coordinates range over the full Hilbert space. The signed coupling counts tuple inversions and vanishes on repeated indices. Only the compatible published CAR predicate and Euclidean operator norm are reused.
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), pp.8–13,17,21; Eqs. (2.1)–(2.14), (3.3)–(3.6), (3.36), (4.5)

import Mathlib
import Definitions.Def_SYKEdge_Majorana
import Definitions.Def_SYKFastMix_FastMixing_Operators

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace SYKFastMix.FastMixing

/-- Section 2 standing assumptions. Every Hermitian CAR representation in the paper's
 dimension is included, after choosing any orthonormal basis. -/
structure Model (N : ℕ) where
  size : 4 ≤ N
  even : Even N
  J : ℝ
  positive : 0 < J
  γ : Fin N → Mat (Fin (2 ^ (N / 2)))
  car : SYKEdge.IsMajoranaFamily γ

abbrev SiteHilbert (N : ℕ) := Fin (2 ^ (N / 2))
abbrev Disorder (N : ℕ) := SYKEdge.KSet N 4 → ℝ
variable {N : ℕ}

def disorderLaw (Q : Model N) : Measure (Disorder N) :=
  Measure.pi (fun _ => gaussianReal 0 (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3)))

def rawString (Q : Model N) (S : Finset (Fin N)) : Mat (SiteHilbert N) :=
  ((S.sort (· ≤ ·)).map Q.γ).prod

def hamiltonian (Q : Model N) (w : Disorder N) : Mat (SiteHilbert N) :=
  ∑ A, (w A : ℂ) • rawString Q A.1

/-- Signed extension of a four-set coupling: the sign counts inversions in the tuple.
 Repeated indices give zero. -/
def coupling (w : Disorder N) (i j k l : Fin N) : ℝ :=
  let v : Fin 4 → Fin N := ![i,j,k,l]
  if h : ({i,j,k,l} : Finset (Fin N)).card = 4 then
    (-1 : ℝ) ^ ((Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2 ∧ v p.2 < v p.1)).card) *
      w ⟨{i,j,k,l}, h⟩
  else 0

def imaginary (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) : Mat (SiteHilbert N) :=
  mexp ((-s : ℂ) • hamiltonian Q w) * Q.γ i * mexp ((s : ℂ) • hamiltonian Q w)

def parityMatrix (Q : Model N) : Mat (SiteHilbert N) :=
  Complex.I ^ (N / 2) • rawString Q Finset.univ

def parity (Q : Model N) (X : Mat (SiteHilbert N)) : Mat (SiteHilbert N) :=
  parityMatrix Q * X * parityMatrix Q

def clifford (Q : Model N) (i : Fin N) : Super (SiteHilbert N) :=
  super (fun X => (1 / 2 : ℂ) • (Q.γ i * X - parity Q X * Q.γ i))

def cMap (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) : Super (SiteHilbert N) :=
  super (fun X => (1 / 2 : ℂ) •
    (imaginary Q w (β/4) i * X - X * (imaginary Q w (β/4) i)ᴴ))
def cfMap (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) : Super (SiteHilbert N) :=
  super (fun X => (1 / 2 : ℂ) •
    (jump (hamiltonian Q w) Q.γ β i * X - X * (jump (hamiltonian Q w) Q.γ β i)ᴴ))
def bMap (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) : Super (SiteHilbert N) :=
  super (fun X => (1 / 2 : ℂ) •
    (imaginary Q w (β/4) i * X - parity Q X * (imaginary Q w (β/4) i)ᴴ))
def unfilteredK (Q : Model N) (w : Disorder N) (β : ℝ) : Super (SiteHilbert N) :=
  ∑ i, (cMap Q w β i)ᴴ * cMap Q w β i
def filteredK (Q : Model N) (w : Disorder N) (β : ℝ) : Super (SiteHilbert N) :=
  ∑ i, (cfMap Q w β i)ᴴ * cfMap Q w β i

def jacobian (Q : Model N) (w : Disorder N) (s : ℝ) : Mat (Fin N × SiteHilbert N) :=
  fun a b => ((1 / 2 : ℂ) • anticomm (Q.γ b.1) (imaginary Q w s a.1)) a.2 b.2

/-- Polarized version of (2.13), also used to take its exact Taylor coefficients. -/
def mBlock (w : Disorder N) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B C D : Fin N → Mat ι) (i j : Fin N) : Super ι :=
  super (fun X => (1 / 3 : ℂ) • ∑ k, ∑ l,
    (coupling w i j k l : ℂ) • (A k * C l * X - A k * X * D l + X * B k * D l))
def blockM (Q : Model N) (w : Disorder N) (s : ℝ) : Mat (Fin N × (SiteHilbert N × SiteHilbert N)) :=
  fun a b => mBlock w (imaginary Q w s) (imaginary Q w (-s))
    (imaginary Q w s) (imaginary Q w (-s)) a.1 b.1 a.2 b.2

end SYKFastMix.FastMixing


