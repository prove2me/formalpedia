-- Prove2me | Definitions.Def_A3X_enclosure
-- name    : A3X_enclosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T01:38:24.069845+00:00
-- url     : https://prove2.me/theorems/007b1ee4-01a2-4e1b-85ec-23039c681b21
-- title:
--   Real-valued meaning and validity of A3X Taylor models
-- statement:
--   The exact source definitions interpret the rational polynomial certificates as real functions. On the original domain, Encl bounds the approximation error by a rational remainder times a power of t; Good adds nonnegativity of that remainder. The bundle also supplies the original coefficient-bound relation, polynomial evaluation, and list truncation operations used by the multiplication soundness proofs. It introduces no analytic claim or numerical certificate.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TMFun.lean#L17

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_A3X_numeric_core



/-!
# CKLaneA3X.Poly — exact sparse polynomials for the high-u Taylor-model checker

Three-level representation (all kernel-evaluable via `List.rec`; no well-founded recursion):
* `LPoly` : Laurent polynomial in `L` (intended `L = log 2`): list of `(c, q)` meaning `q * L^c`.
* `SPoly` : polynomial in `σ` with `LPoly` coefficients: list of `(b, l)` meaning `σ^b * l`.
* `TPoly` : dense polynomial in `t` with `SPoly` coefficients: `[s₀, s₁, …]` means `s₀ + t*(s₁ + t*(…))`.

Only `eval`-soundness matters for the checker; sortedness is used for compactness but never for
soundness.
-/

namespace CKLaneA3X





/-! ## LPoly -/

noncomputable def LPoly.eval (L : ℝ) (l : LPoly) : ℝ :=
  @List.rec (ℤ × ℚ) (fun _ => ℝ) 0 (fun m _ ih => (m.2 : ℝ) * L ^ m.1 + ih) l
























/-! ## SPoly -/

noncomputable def SPoly.eval (σ L : ℝ) (s : SPoly) : ℝ :=
  @List.rec (ℕ × LPoly) (fun _ => ℝ) 0 (fun m _ ih => σ ^ m.1 * LPoly.eval L m.2 + ih) s
























/-! ## TPoly (dense in t) -/

noncomputable def TPoly.eval (t σ L : ℝ) (P : TPoly) : ℝ :=
  @List.rec SPoly (fun _ => ℝ) 0 (fun s _ ih => SPoly.eval σ L s + t * ih) P




















/-- `t`-coefficient list truncation (first `k` entries). -/
noncomputable def TPoly.take (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => TPoly) [] (fun k' _ => s :: ih k') k) P

noncomputable def TPoly.drop (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s P' ih => fun k => Nat.rec (motive := fun _ => TPoly) (s :: P') (fun k' _ => ih k') k) P










end CKLaneA3X



/-!
# CKLaneA3X.Bound — rigorous magnitude bounds for `LPoly`/`SPoly`/`TPoly`

`L` ranges over `[Llo, Lhi]` (Mathlib `Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `|σ| ≤ 1/2`,
`0 ≤ t ≤ Tq`.  All bound functions are kernel-evaluable (`List.rec`/`Nat.rec`).
-/

namespace CKLaneA3X



































/-! ## entry bounds for TPoly -/

/-- `EntryBnd P β`: `β` bounds every t-coefficient of `P` in absolute value (same length). -/
def EntryBnd (P : TPoly) (β : List ℚ) : Prop :=
  List.Forall₂ (fun (s : SPoly) (b : ℚ) => ∀ σ : ℝ, |σ| ≤ 1 / 2 → |SPoly.eval σ (Real.log 2) s| ≤ (b : ℝ)) P β









/-! ## sums of entry bounds -/









def Nonneg (β : List ℚ) : Prop := ∀ b ∈ β, 0 ≤ b











end CKLaneA3X



/-!
# CKLaneA3X.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3X

def Dom (t ρ : ℝ) : Prop := 0 < t ∧ t ≤ (Tq : ℝ) ∧ 0 < ρ ∧ ρ < 1





noncomputable def ev (P : TPoly) (t ρ : ℝ) : ℝ := TPoly.eval t (ρ - 1 / 2) (Real.log 2) P

def Encl (f : ℝ → ℝ → ℝ) (P : TPoly) (r : ℚ) (n : ℕ) : Prop :=
  ∀ t ρ, Dom t ρ → |f t ρ - ev P t ρ| ≤ (r : ℝ) * t ^ n















/-! ## zero prefix (valuation) -/







/-! ## truncated product soundness -/













/-! ## division by t, truncation -/





end CKLaneA3X



/-!
# CKLaneA3X.TMFun — functional Taylor-model operations (kernel-evaluable) with soundness

A `TMd` is `(P, r, n)`.  `Good f d` := `Encl f d.P d.r d.n ∧ 0 ≤ d.r`.
All remainders are rounded up to multiples of `2^-40` (`rup`) to keep rationals small.
-/

namespace CKLaneA3X



def Good (f : ℝ → ℝ → ℝ) (d : TMd) : Prop := Encl f d.P d.r d.n ∧ 0 ≤ d.r





































/-! ## Horner evaluation of a rational polynomial at a TM -/












/-! ## magnitude of a TM-enclosed function -/



end CKLaneA3X


