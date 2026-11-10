-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
-- name    : SymmetricPSM1041_ORLowerBound_CostsRestrictions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:03.755971+00:00
-- url     : https://prove2.me/theorems/8bba3c84-ddf1-41e5-86b1-fb9d4d374eb7
-- title:
--   §2.2 — actual alphabets, total cost and arbitrary restrictions
-- statement:
--   For a protocol $P$, let $\mathcal A_i(P)=\{M_i(b,r):b\in\{0,1\},\ r\in R\}$ be the actual local alphabet. The length and total cost are
--
--   $$\ell_P(x,r)=\sum_i |M_i(x_i,r)|,\qquad \operatorname{cost}(P)=\max_{x,r}\ell_P(x,r).$$
--
--   The two privacy classes are perfect privacy and support privacy. For an integer $b\ge0$, the predicate $\operatorname{IndividualLowerBound}(\rho,f,b)$ means that every perfectly correct protocol for $f$ in class $\rho$ has a party $i$ with $|\mathcal A_i(P)|\ge2^b$. For nonempty party sets, this is exactly $C_{\rm indiv}(f)\ge b$, since the logarithms are base two. Equivalently, protocols whose every actual alphabet has size at most $2^b-1$ are excluded. Trimming unused declared symbols preserves correctness and either privacy class.
--
--   For any coordinate subset $I$ and full assignment $z$, the restriction has input space $\{0,1\}^I$ and is
--
--   $$f_{I,z}(y)=f(u),\qquad u_i=\begin{cases}y_i&i\in I,\\z_i&i\notin I.\end{cases}$$
--
--   This separates actual transcript length from alphabet cardinalities, and supports the exact lifting lemma. The maximum is taken over a finite nonempty set of input-seed pairs. No minimum over a universe of protocols and no logarithm of zero is used. The individual lower-bound predicate is used only on nonempty coordinate sets in Lemma 6.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), pp. 7–9, §2.2, communication metrics, restrictions and Lemma 6

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_PSM

namespace SymmetricPSM1041.ORLowerBound

inductive PrivacyClass where
  | perfect
  | support

def HasPrivacy {ι : Type*} (ρ : PrivacyClass) (P : PSM ι)
    (f : (ι → Bool) → Bool) : Prop :=
  match ρ with
  | .perfect => PerfectPrivate P f
  | .support => SupportPrivate P f

/-- The exact alphabet of messages actually used by party i, allowing empty strings. -/
noncomputable def localAlphabet {ι : Type*} (P : PSM ι) (i : ι) : Finset Message := by
  classical
  exact Finset.univ.image (fun br : Bool × Fin P.seedCount => (P.message i br.1 br.2).val)

def transcriptLength {ι : Type*} [Fintype ι] (P : PSM ι)
    (x : ι → Bool) (r : Fin P.seedCount) : ℕ :=
  ∑ i, ((P.message i (x i) r).val).length

noncomputable def totalCost {ι : Type*} [Fintype ι] (P : PSM ι) : ℕ := by
  classical
  exact Finset.univ.sup
    (fun xr : (ι → Bool) × Fin P.seedCount => transcriptLength P xr.1 xr.2)

/-- For natural b, C_indiv(f) ≥ b: every admissible protocol has a local alphabet
of cardinality at least 2^b. No bound is imposed on the seed count. -/
def IndividualLowerBound {ι : Type*} (ρ : PrivacyClass)
    (f : (ι → Bool) → Bool) (b : ℕ) : Prop :=
  ∀ P : PSM ι, PerfectCorrect P f → HasPrivacy ρ P f →
    ∃ i : ι, 2 ^ b ≤ (localAlphabet P i).card

/-- Every coordinate outside I is fixed according to z; the domain is exactly the free
coordinates I, not a cylinder in the original input space. -/
noncomputable def restrictFunction {ι : Type*} (f : (ι → Bool) → Bool)
    (I : Finset ι) (z : ι → Bool) : (I → Bool) → Bool := by
  classical
  exact fun y => f (fun i => if h : i ∈ I then y ⟨i, h⟩ else z i)

end SymmetricPSM1041.ORLowerBound


