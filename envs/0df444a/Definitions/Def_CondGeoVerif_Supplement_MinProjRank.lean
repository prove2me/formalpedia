-- Prove2me | Definitions.Def_CondGeoVerif_Supplement_MinProjRank
-- name    : CondGeoVerif_Supplement_MinProjRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:44.542722+00:00
-- url     : https://prove2.me/theorems/99b6ab8e-d382-4a45-a89e-470d0d8fb924
-- title:
--   Gaussian prevalence, minimum projection rank and minimum polynomial threshold degree of a predictor
-- statement:
--   For a predictor $h:\mathbb R^d\to\{-1,1\}$ and $X\sim N(0,I_d)$:
--
--   1. the **Gaussian positive prevalence** of $h$ is $P(h(X)=+1)$;
--   2. $h$ has **minimum projection rank** $r$ if $h$ agrees almost everywhere with $x\mapsto g(P^\top x)$ for some Borel $g:\mathbb R^r\to\{-1,1\}$ and some $P\in\mathbb R^{d\times r}$, and with no such function for a smaller $r$;
--   3. $h$ has **minimum polynomial threshold degree** $n$ if $\mathrm{sign}(p(x))=h(x)$ almost everywhere for some nonzero real polynomial $p$ of degree at most $n$, and for no nonzero polynomial of smaller degree.
--
--   These are the structural measures of class complexity matched in Theorem 4.3 and Lemma C.12.
--
--   **Formalization Note** Both notions are read up to Gaussian-null sets, as in the proof of Lemma C.12. The sign of $0$ is $+1$; a nonzero polynomial vanishes only on a null set.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem 4.3, p.9 (PDF p.12); Lemma C.12 and its proof, pp.36–37 (PDF pp.39–40)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

namespace CondGeoVerif.Supplement

noncomputable section

open MeasureTheory CondGeoVerif
open scoped Matrix

/-- The **Gaussian positive prevalence** `P(h(X) = +1)`, `X ∼ N(0, I_d)` (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, Theorem 4.3,
p.9 = PDF p.12; Lemma C.12, p.36). -/
noncomputable def posPrevalence {d : ℕ} (h : Vec d → Bool) : ℝ :=
  (gauss d {x | h x = true}).toReal

/-- `h` **depends on a rank-`r` projection**: it agrees almost everywhere under `N(0, I_d)` with
`x ↦ g(Pᵀx)` for some Borel `g : ℝʳ → {−1, 1}` and some matrix `P ∈ ℝ^{d×r}` (Chen, Oct. 2026,
Lemma C.12 and its proof, pp.36–37 = PDF pp.39–40: "If the predictor were a function of a projection
onto a subspace L …"). -/
def ProjRepr {d : ℕ} (h : Vec d → Bool) (r : ℕ) : Prop :=
  ∃ g : Vec r → Bool, Measurable g ∧ ∃ P : Matrix (Fin d) (Fin r) ℝ,
    h =ᵐ[gauss d] fun x => g (matVec Pᵀ x)

/-- **Minimum projection rank** `r` (Chen, Oct. 2026, Theorem 4.3, p.9; Lemma C.12, p.36): `h`
depends on a rank-`r` projection and on no projection of smaller rank.

**Formalization Note** Projection rank is read up to Gaussian-null sets, as in the proof of
Lemma C.12 ("would preserve it almost everywhere"). -/
def MinProjRank {d : ℕ} (h : Vec d → Bool) (r : ℕ) : Prop :=
  ProjRepr h r ∧ ∀ r' : ℕ, r' < r → ¬ ProjRepr h r'

/-- `h` is a **polynomial threshold function of degree at most `n`**: there is a nonzero real
polynomial `p` on `ℝᵈ` of total degree at most `n` with `sign(p(x)) = h(x)` for almost every `x`
under `N(0, I_d)` (Chen, Oct. 2026, Lemma C.12 and its proof, p.37 = PDF p.40: "Any nonzero
polynomial whose sign agrees almost everywhere with the predictor"). -/
def PTFRepr {d : ℕ} (h : Vec d → Bool) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin d) ℝ, p ≠ 0 ∧ p.totalDegree ≤ n ∧
    ∀ᵐ x ∂(gauss d), h x = decide (0 ≤ MvPolynomial.eval (fun i => x i) p)

/-- **Minimum polynomial threshold degree** `n` (Chen, Oct. 2026, Theorem 4.3, p.9; Lemma C.12,
p.36): `h` is a polynomial threshold function of degree at most `n` and of no smaller degree.

**Formalization Note** The sign of `0` is `+1`; a nonzero polynomial vanishes only on a Gaussian-
null set, so this convention does not matter. -/
def MinPTFDegree {d : ℕ} (h : Vec d → Bool) (n : ℕ) : Prop :=
  PTFRepr h n ∧ ∀ n' : ℕ, n' < n → ¬ PTFRepr h n'

end

end CondGeoVerif.Supplement


