-- Prove2me | Definitions.Def_InfoLossLAR_RegevSketch_DGS
-- name    : InfoLossLAR_RegevSketch_DGS
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:11:44.097007+00:00
-- url     : https://prove2.me/theorems/e2cb1d57-b867-47fa-8bb7-2003b65f91b2
-- title:
--   Concrete joint-output lattice Gaussian sampling contract
-- statement:
--   For an integer basis matrix $B$ of dimension $n$, let $L(B)$ be its column lattice. Set
--
--   $$
--   \epsilon(n)=2^{-\operatorname{size}(n+2)^2},\qquad
--   \Phi(B)=\frac{16q(n)\sqrt n}{\sigma(n)}\eta_{\epsilon(n)}(L(B)).
--   $$
--
--   Here $q(n)$ and $\sigma(n)$ are the fixed public-family modulus and Gaussian width, and $\eta$ is the published smoothing parameter. The binary size in $\epsilon$ is the usual natural-number bit length.
--
--   The coefficient law at positive width $r$ assigns to $z\in\mathbb Z^n$ mass proportional to $\exp(-\pi\|Bz\|^2/r^2)$. The input encoding specifies $B$, a positive rational width $r$, a unary sample count $m$, and a unary inverse numerical-error budget $u$. A successful output begins with the canonical encoding of the complete pool of $m$ original-basis coefficient vectors.
--
--   The predicate $\mathrm{DGSAt}(G,n,\delta)$ states that, for every nonsingular $B$, every $r\ge\Phi(B)$ and every event on the complete pool, the difference between the actual output-event probability of the published multi-output circuit family $G$ and the independent Gaussian product probability is at most
--
--   $$
--   m\delta+\frac1{u+1}.
--   $$
--
--   This package defines the sampling contract and encodings only. It makes no claim that a sampler, BDD decoder, or lattice reduction exists. The constant slack and explicit bit encodings specialize the source's DGS interface to the fixed Gaussian-LWE family.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Definition 2.10 and Theorem 3.1 (DGS and smoothing); original-basis coefficient encoding and explicit unary numerical budget are formalization interfaces for InfoLossLAR.WorstCase.fixed_family_gaussian_lwe_worst_case.

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_RegevLWE_GaussConv_Lattice

set_option autoImplicit false
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch
noncomputable section

/-- The actual integer input lattice, as a Z-submodule for smoothing. -/
def inputModule {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (fun i : Fin n => latVec B (Pi.single i 1)))

/-- One fixed negligible smoothing schedule; independent of the adversary. -/
def smoothingError (n : ℕ) : ℝ := 1/(2 : ℝ)^((Nat.size (n+2))^2)

/-- Regev's DGS threshold, with an absolute slack constant and alpha=sigma/q.
The square-root is an analysis parameter; samplers receive rational widths. -/
def dgsThreshold {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  (16*(famq n : ℝ)*Real.sqrt n/(famσ n : ℝ))*
    RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n)

/-- True normalized coefficient law of D_(L(B),r), using the original B. -/
def coefficientMass {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (z : Fin n → ℤ) : ℝ :=
  rhoInt r (B.mulVec z)/(∑' y : Fin n → ℤ,rhoInt r (B.mulVec y))

/-- Unary count and inverse-error budget keep the requested output and
approximation work inside the native input size. -/
def dgsInput {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (count budget : ℕ) : Str :=
  encPair (encMat encI B) (encPair (encQ r) (encPair (unary count) (unary budget)))

/-- The actual measured output must encode the whole original-basis
coefficient pool before any event on the pool is tested. -/
def decodedPoolEvent {n count : ℕ} (event : (Fin count → Fin n → ℤ) → Prop) (out : Str) : Prop :=
  ∃ pool : Fin count → Fin n → ℤ,encVec (encVec encI) pool <+: out ∧ event pool

/-- Complete joint DGS correctness for one actual multi-output family.
This is a problem contract, not an existence assumption: all missing
algorithmic existence claims are explicit open child theorems. -/
def DGSAt (A : MFamily) (n : ℕ) (error : ℝ) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) ℤ,B.det ≠ 0 →
    ∀ r : ℚ,0 < r → dgsThreshold B ≤ (r : ℝ) →
      ∀ count budget : ℕ,∀ event : (Fin count → Fin n → ℤ) → Prop,
        |outputProb A (dgsInput B r count budget) (decodedPoolEvent event)-
          ∑' pool : Fin count → Fin n → ℤ,
            (∏ i,coefficientMass B r (pool i))*(if event pool then 1 else 0)| ≤
              (count : ℝ)*error+1/((budget : ℝ)+1)

end
end InfoLossLAR.WorstCase.RegevSketch


