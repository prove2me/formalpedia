-- Prove2me | Definitions.Def_LowAccLTC_kmsCode
-- name    : LowAccLTC_kmsCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:52.907985+00:00
-- url     : https://prove2.me/theorems/184cc1af-f646-45a3-8073-ee65f8c72d98
-- title:
--   KMS codes $C(q,r,d,m)$: degree-$\le d$ polynomials on every line
-- statement:
--   On the KMS complex $X(q,r,m)$, the star of every co-rank-one face $u$ is an affine line over $\mathbb F_q$ inside $M_r(R)$ viewed as an $\mathbb F_q$-vector space ($q$ top faces). The local code $C_u$ consists of the evaluations of univariate polynomials of degree at most $d$ on this line, the line being identified with $\mathbb F_q$ by an affine parametrization $a\mapsto g_0+aD$; the code does not depend on this choice, since invertible affine changes of variable preserve the degree bound. The **KMS code** is the HDX code
--   $$C(q,r,d,m)=\mathrm{Tan}\big(X(q,r,m),\{C_u\}_{u\in X\langle r-1\rangle}\big),$$
--   the words $f:\Gamma\to\mathbb F_q$ whose restriction to every co-rank-one star is a polynomial of degree at most $d$.
--
--   These are the codes of the goal theorem (with $q=p$ prime and $C_u=\mathrm{RS}(p,d)$).
--
--   **Formalization Note** A word $h$ on $\mathrm{star}(u)$ is in $C_u$ iff some $g_0,D$ and some $P$ of degree $\le d$ satisfy: every $x\in\mathrm{star}(u)$ equals $g_0+aD$ with $h(x)=P(a)$. Since the star is a line with $q$ points, such a parametrization is a bijection $\mathbb F_q\to\mathrm{star}(u)$ (footnote 9).
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 3.1 and footnote 9, p.24 (PDF p.27); line structure p.23 (PDF p.26)

import Definitions.Def_LowAccLTC_kmsComplex
import Definitions.Def_LowAccLTC_TannerCode

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

variable {F : Type*} [Field F] (r : ℕ) (ϕ : Polynomial F)
  [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)]

/-- The local line codes of the KMS code (Definition 3.1, p.24, with footnote 9): on the star of
a co-rank-one face `u` of the KMS complex, which is an affine line over `F` (p.23: "every
codimension-one star is an affine line containing q top-faces"), `C_u` consists of the
evaluations of univariate polynomials of degree at most `d` on the line, the line being
identified with `F` by an affine parametrization `a ↦ g₀ + a·D` inside `M_r(R)` viewed as an
`F`-vector space.

**Formalization Note.** A word `h` on `star(u)` is in `C_u` iff there are `g₀, D ∈ M_r(R)` and a
polynomial `P` with `deg P ≤ d` such that every point `x ∈ star(u)` has the form `g₀ + a·D` with
`h(x) = P(a)`. Since `star(u)` is a line with `q` points, any such parametrization is a
bijection `F → star(u)` and, as footnote 9 says, the code does not depend on its choice
(affine changes of variable preserve the degree bound). The definition is applied by `localCode`
only to co-rank-one faces. -/
def kmsLineCodes (d : ℕ) :
    (u : Finset (Fin r × Set (KMSGamma r ϕ))) → Set ((kmsComplex r ϕ).star u → F) :=
  fun u => {h | ∃ (g₀ D : Matrix (Fin r) (Fin r) (AdjoinRoot ϕ)) (P : Polynomial F),
    P.natDegree ≤ d ∧ ∀ x : (kmsComplex r ϕ).star u, ∃ a : F,
      ((x.1 : KMSGamma r ϕ) : Matrix (Fin r) (Fin r) (AdjoinRoot ϕ)) = g₀ + AdjoinRoot.of ϕ a • D ∧
      h x = P.eval a}

/-- The KMS code `C(q, r, d, m) = Tan(X(q, r, m), {C_s}_{s ∈ X⟨r-1⟩})` (Definition 3.1, p.24):
the words `f : Γ → F` whose restriction to every co-rank-one star (an affine line) is the
evaluation of a polynomial of degree at most `d`. -/
def kmsCode (d : ℕ) : Set (KMSGamma r ϕ → F) := (kmsComplex r ϕ).tanner (kmsLineCodes r ϕ d)

end LowAccLTC


