-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_FiniteLocusCandidates
-- name    : WeierstrassEllipticZeta_FiniteLocusCandidates
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T06:28:39.541081+00:00
-- url     : https://prove2.me/theorems/e02d144c-26ad-4686-8cb5-8d94969a9ae8
-- title:
--   Finite elementary-locus candidates and period-scaled samples
-- statement:
--   For a period submodule $\Lambda\subseteq\mathbb C$ and finite input $X$, define
--   $P_\Lambda(X)=\{(x,y)\in X^2:x\ne y,\ x-y\in\Lambda\}$.
--   The candidate type consists of one point candidate, one whole-fibre candidate,
--   and one line candidate for each ordered pair in $P_\Lambda(X)$.
--
--   Given the additive quasiperiod map $\eta:\Lambda\to\mathbb C$, the line for
--   $(x,y)$ has slope $\eta(\delta)/\delta$, where $\delta=x-y$.
--   At anchor $r\in\mathbb C^3$ its sample points are
--   $r+(j\delta,0,j\eta(\delta))$ for $0\le j\le m+n$.
--   The point and whole-fibre candidates use the established elementary-locus
--   samples. The nonzero denominator follows from $x\ne y$.
--
--   These definitions introduce a finite set of possible shapes and slopes. They
--   do not select an anchor or establish the A.1 global cost bound. The finite set
--   uses classical decidability of equality and period membership; no effective
--   algorithm for those decisions is asserted.
-- source:
--   Derived finite-candidate selection for the A.1 frontier in https://prove2.me/theorems/863bfa22-6f5f-421e-ad37-5ebe13eb142a. Source motivation: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A, proof of Proposition A.1, case (4), equation (A.16): distinct representatives in one quotient class give a nonzero period. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. Together with the already formalized elementary line kernel {omega in Lambda : eta(omega)=alpha*omega}, this yields the derived slope alpha=eta(x-y)/(x-y). Root counting proves equivalence of period-scaled and canonical samples. The finite-candidate theorem is proved here without platform theorem dependencies. It is not the paper's global zero estimate. Both frontier directions preserve C, the anchor, chart point, cost and class count; a line without collisions may become a point. The anchor and global cost inequality remain Open. No numerical integer-search improvement is claimed.

import Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- Distinct pairs in the finite input whose difference is a period. -/
def periodPairCandidates (Λ : Submodule ℤ ℂ) (X : Finset ℂ) : Finset (ℂ × ℂ) :=
  X.offDiag.filter (fun p => p.1 - p.2 ∈ Λ)

/-- Point, full fibre, or the line determined by a period pair. -/
abbrev FiniteLocusCandidate (Λ : Submodule ℤ ℂ) (X : Finset ℂ) :=
  Unit ⊕ (Unit ⊕ ↥(periodPairCandidates Λ X))

/-- The period and quasiperiod displacement attached to a finite pair. -/
def candidatePeriod (Λ : Submodule ℤ ℂ) (X : Finset ℂ)
    (p : ↥(periodPairCandidates Λ X)) : Λ :=
  ⟨p.val.1 - p.val.2, (Finset.mem_filter.mp p.property).2⟩

def candidateLocusShape (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ) :
    FiniteLocusCandidate Λ X → ElementaryLocusShape
  | .inl _ => .point
  | .inr (.inl _) => .fibre
  | .inr (.inr p) => .line (η (candidatePeriod Λ X p) / (candidatePeriod Λ X p : ℂ))

/-- Candidate line samples follow the actual period/quasiperiod displacement.
The point and fibre samples retain their usual normalizations. -/
def candidateLocusSamples (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (k : FiniteLocusCandidate Λ X) (r : Fin 3 → ℂ) (m n : ℕ) :
    Finset (Fin 3 → ℂ) :=
  match k with
  | .inl _ => {r}
  | .inr (.inl _) => elementaryLocusSamples .fibre r m n
  | .inr (.inr p) =>
      (Finset.range (m + n + 1)).image (fun j : ℕ =>
        r + ![(j : ℂ) * (candidatePeriod Λ X p : ℂ), 0,
          (j : ℂ) * η (candidatePeriod Λ X p)])

end WeierstrassEllipticZeta


