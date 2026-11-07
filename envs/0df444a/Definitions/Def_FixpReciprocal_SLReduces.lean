-- Prove2me | Definitions.Def_FixpReciprocal_SLReduces
-- name    : FixpReciprocal_SLReduces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:13.330208+00:00
-- url     : https://prove2.me/theorems/cd4df4f3-3ce4-4565-add8-ed85ff5a2540
-- title:
--   SL-reduction (Definition 3.2)
-- statement:
--   Let $\Pi$ and $\Gamma$ be search problems with real-valued solution sets. A **separable-linear reduction** (SL-reduction) from $\Pi$ to $\Gamma$ consists of a polynomial-time map taking each instance $\mathcal I$ of $\Pi$ to an instance $\mathcal J=\mathcal J(\mathcal I)$ of $\Gamma$, together with indices $\rho(i)$ and rationals $a_i,b_i$ computable in polynomial time from $\mathcal I$, such that every $y\in\mathrm{Sol}_\Gamma(\mathcal J)$ gives a vector $x\in\mathrm{Sol}_\Pi(\mathcal I)$ defined by
--   $$x_i=a_i\,y_{\rho(i)}+b_i.$$
--
--   Each source coordinate is recovered by an affine function of a single target coordinate. This is the notion of reduction under which FIXP and FIXP-completeness are defined.
--
--   **Formalization Note** Polynomial time is `Turing.TM2ComputableInPolyTime` for the fixed encodings of the two problems. The data $(\rho(i),a_i,b_i)_i$ is one output list, of length $n(\mathcal I)$, with indices below the dimension of $\mathcal J$. One machine replaces three; they are equivalent up to projecting the list.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Definition 3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace FixpReciprocal

open OnlineCRS.Combine

/-- Encoding of recovery data: the list of triples `(ρ(i), a_i, b_i)`, binary. -/
def encRecovery : List (ℕ × ℚ × ℚ) → List Sym :=
  fList (fun e => fNat e.1 ++ fRat e.2.1 ++ fRat e.2.2)

/-- **Separable-linear recovery.** The vector `x ∈ ℝⁿ` with `x_i = a_i y_{ρ(i)} + b_i`, for recovery
data `r = [(ρ(0), a_0, b_0), …]`. -/
noncomputable def recover {m : ℕ} (n : ℕ) (r : List (ℕ × ℚ × ℚ)) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun i =>
    let e := r.getD i.val (0, 0, 0)
    (e.2.1 : ℝ) * lookup y e.1 + (e.2.2 : ℝ)

/-- **SL-reduction (Definition 3.2).** A polynomial-time map `I ↦ J(I)`, together with indices `ρ(i)`
and rationals `a_i, b_i` computable in polynomial time from `I`, such that every `y ∈ Sol_Γ(J(I))`
gives a vector `x ∈ Sol_Π(I)` defined by `x_i = a_i y_{ρ(i)} + b_i`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.2, p.10.

**Formalization Note.** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` for the two
problems' fixed encodings, a machine per reduction. The data `ρ, a, b` is one output list `r I`,
of length `dim I`, with indices below the dimension of `J I` (one machine rather than three; the two
are equivalent up to a projection of the list). The quantifier over `y` is universal and each `x_i`
depends on one coordinate of `y` only. -/
def SLReduces (P Q : RealSearch) : Prop :=
  ∃ (J : P.Inst → Q.Inst) (r : P.Inst → List (ℕ × ℚ × ℚ)),
    Nonempty (Turing.TM2ComputableInPolyTime P.enc Q.enc J) ∧
    Nonempty (Turing.TM2ComputableInPolyTime P.enc encRecovery r) ∧
    ∀ I : P.Inst,
      (r I).length = P.dim I ∧
      (∀ e ∈ r I, e.1 < Q.dim (J I)) ∧
      ∀ y ∈ Q.Sol (J I), recover (P.dim I) (r I) y ∈ P.Sol I

end FixpReciprocal


