-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch
-- name    : InfoLossLAR_RegevSearch
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:10:04.186213+00:00
-- url     : https://prove2.me/theorems/ffa59115-c72b-4438-bc15-c737a01414a6
-- title:
--   Fixed-family Gaussian LWE search on an infinite parameter set
-- statement:
--   For a multi-output quantum family $A$, a polynomial sample-count $m$, a cutoff $n_0$, and a set $S$ of parameters, the predicate $\operatorname{SearchOn}(A,m,n_0,S)$ requires a success probability at least $3/4$ for every $n\in S$ with $n\ge n_0$ and every secret. The probability is taken over a fresh table of $m(n)$ independent fixed-family Gaussian LWE blocks and the measurement of $A$ on that table's actual encoding. The decoded output must equal the entire secret vector.
--
--   The predicate records one fixed searcher and one polynomial that work for the whole set. It does not require any independence between repeated calls using a shared sample pool.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136, Appendix I.1; Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, §§3.2 and 4.2. This is a fixed-family, explicit encoding and circuit-model interface.

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_04
import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
noncomputable section
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open Integration9_9.LoadedBatch.Schedule Integration9_9.LARPlatformEncoding
namespace InfoLossLAR.WorstCase.RegevSearch

/-- A uniform searcher recovers each fixed secret with probability at least
3/4 from one fresh fixed-family Gaussian LWE table of a public polynomial
length, for each sufficiently large security parameter in S. -/
def SearchOn (A : MFamily) (samples : Polynomial ℕ) (cutoff : ℕ) (S : Set ℕ) : Prop :=
  ∀ n ∈ S, cutoff ≤ n → ∀ secret : Fin (famN n) → ZMod (famq n),
    (3/4 : ℝ) ≤ (larObservedRealTableLaw (famq n) (famN n) (famd n) (samples.eval n)
      (fixedGaussianSource (famd n) n) secret).expectation (fun pool =>
      outputProb A (encInput n (famPP n) (encTable pool))
        (fun output => (readVector output).2=List.ofFn (fun i => (secret i).val)))
end InfoLossLAR.WorstCase.RegevSearch


