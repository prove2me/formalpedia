-- Prove2me | Definitions.Def_PreservePast_Supplement_HidesRecords
-- name    : PreservePast_Supplement_HidesRecords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:28:36.912543+00:00
-- url     : https://prove2.me/theorems/6faa3ac6-db50-49f8-a56d-f0f9c83ab55c
-- title:
--   Deterministic nearest-of-$k$ protocols, conditional entropy in bits, and the record-hiding properties (238)–(239)
-- statement:
--   For a deterministic encoder $M=\mathrm{enc}(X)$ of the uniform database $X\in(\{-1,1\}^d)^k$ into a finite alphabet and a deterministic decoder, the **success** is $\Pr\{\hat J(M,Z)=J\}$ in the nearest-of-$k$ experiment.
--
--   For functions $f,g$ of a uniform variable on a finite set, $H(f\mid g)$ denotes **conditional entropy in bits**.
--
--   The encoder **hides records at level $r$** if, for every record index $j$,
--
--   1. $H(X_j\mid M)=r$;
--   2. every estimator $\hat X_j(M)$, with independent randomization, satisfies $\Pr\{\hat X_j(M)=X_j\}\le 2^{-r}$;
--   3. for every $\eta>0$, every such estimator satisfies
--   $$\Pr\{\operatorname{dist}_H(X_j,\hat X_j(M))\le(\tfrac12-\eta)d\}\le\exp\Big(-\frac{2\eta^2r}{1+r/d}\Big);$$
--
--   and moreover the whole-dataset information is $k(d-r)$ bits (that is, $H(X\mid M)=kr$) and $kr$ additional helper bits recover the database exactly.
--
--   These are the conclusions (238)–(239) of Theorem 19.
--
--   **Formalization Note** Probabilities are averages over the uniform database of the estimator's coin probability. "Helper bits recover it exactly" is the injectivity of $x\mapsto(\mathrm{enc}(x),\mathrm{helper}(x))$ for some helper with $2^{kr}$ values.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 19, p.65 (PDF p.67), eqs. (238)–(239); Definition 1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The **success probability of a deterministic protocol** for the nearest-of-k experiment
(Definition 1, p.10): encoder `enc : database → message`, decoder
`dec : message → query → index`, no coins. -/
noncomputable def detIdSuccess {k d : ℕ} {Msg : Type} (enc : (Fin k → Fin d → Bool) → Msg)
    (dec : Msg → (Fin d → Bool) → Fin k) (ρ : ℝ) : ℝ :=
  ((2 : ℝ) ^ (k * d))⁻¹ * ∑ x : Fin k → Fin d → Bool, ((k : ℝ))⁻¹ * ∑ j : Fin k,
    ∑ z : Fin d → Bool, bscLaw ρ (x j) z * (if dec (enc x) z = j then 1 else 0)

/-- **Conditional entropy in bits** `H(f(X) | g(X))` for `X` uniform on a finite type:
`Σ_{a,m} p(a,m) log₂(p(m)/p(a,m))`, with `p` the counting probabilities and the convention
`0 log 0 = 0` (a term with `p(a,m) = 0` is `0` in Lean). -/
noncomputable def condEntropyBits {𝒳 A M : Type} [Fintype 𝒳] [Fintype A] [Fintype M]
    (f : 𝒳 → A) (g : 𝒳 → M) : ℝ :=
  ∑ m : M, ∑ a : A,
    ((Finset.univ.filter fun x => f x = a ∧ g x = m).card / (Fintype.card 𝒳 : ℝ)) *
      Real.logb 2 (((Finset.univ.filter fun x => g x = m).card : ℝ) /
        (Finset.univ.filter fun x => f x = a ∧ g x = m).card)

/-- **The record-hiding properties of the encoder of Theorem 19.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 19, p.65
(PDF p.67), (238)–(239), for a deterministic encoder `enc` of the uniform database into a finite
alphabet and a number `r` of blocks: for every record index `j`,
* `H(X_j | M) = r` bits;
* every estimator of `X_j` from `M`, with independent randomization, is exactly right with
  probability at most `2^{−r}`;
* for every `η > 0`, every such estimator is within Hamming distance `(1/2 − η)d` of `X_j` with
  probability at most `exp(−2η²r/(1 + r/d))`;
and the whole-dataset information is `k(d − r)` bits (`H(X | M) = kr`, `H(X) = kd`), and `kr`
additional helper bits recover the database exactly.

**Formalization Note.** Probabilities are over the uniform database and the estimator's own coin
space `(Ω, P)`, written as the average over databases of the coin probability. -/
def HidesRecords {k d N : ℕ} (r : ℕ) (enc : (Fin k → Fin d → Bool) → Fin N) : Prop :=
  (∀ j : Fin k, condEntropyBits (fun x : Fin k → Fin d → Bool => x j) enc = r) ∧
  (∀ (j : Fin k) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (est : Fin N → Ω → Fin d → Bool), (∀ M, Measurable (est M)) →
      ((2 : ℝ) ^ (k * d))⁻¹ * ∑ x : Fin k → Fin d → Bool, (P {ω | est (enc x) ω = x j}).toReal ≤
        (2 : ℝ) ^ (-(r : ℝ)) ∧
      ∀ η : ℝ, 0 < η →
        ((2 : ℝ) ^ (k * d))⁻¹ * ∑ x : Fin k → Fin d → Bool,
            (P {ω | (hammingDist (est (enc x) ω) (x j) : ℝ) ≤ (1 / 2 - η) * d}).toReal ≤
          Real.exp (-2 * η ^ 2 * r / (1 + r / d))) ∧
  condEntropyBits (fun x : Fin k → Fin d → Bool => x) enc = k * r ∧
  ∃ helper : (Fin k → Fin d → Bool) → Fin (2 ^ (k * r)),
    Function.Injective fun x => (enc x, helper x)

end PreservePast.Supplement


