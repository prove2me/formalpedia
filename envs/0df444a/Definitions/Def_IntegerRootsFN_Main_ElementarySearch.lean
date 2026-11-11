-- Prove2me | Definitions.Def_IntegerRootsFN_Main_ElementarySearch
-- name    : IntegerRootsFN_Main_ElementarySearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:35.836267+00:00
-- url     : https://prove2.me/theorems/dcb4b918-f81f-4894-a526-03681a5b7d0d
-- title:
--   Coefficient Graeffe transform, exclusion test and elementary search
-- statement:
--   For an integer polynomial $p$, the Graeffe transform is formed from the even coefficients of $(-1)^{\deg p}p(x)p(-x)$, so
--
--   $$Gp(x^2)=(-1)^{\deg p}p(x)p(-x).$$
--
--   For degree $d\ge1$, let $N=\lceil\log_2\log_2(2d)\rceil$. At an integer center $m$ and radius $r\ge1$, Test forms $p(x)=g(m+rx)$, then $q=G^Np$, and answers empty exactly if $|q_0|>\sum_{j\ge1}|q_j|$. In particular $N=0$ at $d=1$.
--
--   The actual search starts at scale $2^b$ with center zero. It discards precisely the centers answering empty for radius $h+2$, splits each remaining center into $m-h/2,m+h/2$, and halves the scale. After exactly $b$ halvings it returns the distinct integers $m-1,m,m+1$ at the kept scale-one centers. An additional definition filters the union with $-1,0,1$ by exact evaluation of $f$.
--
--   The recursive fuel specifies the finite source search; no candidate-set existence or coverage property is assumed. All divisions by two in a valid nonterminal search state are exact.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), pp. 12–13, Appendix A, Test and The search

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- The coefficient-defined Graeffe transform, including (-1)^degree. -/
noncomputable def graeffe (p : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial j
      (((-1 : ℤ) ^ p.natDegree *
        (p * p.comp (-Polynomial.X)).coeff (2 * j)))

/-- ceil(log₂ log₂(2d)), equal to zero when d=1. -/
noncomputable def graeffeCount (d : ℕ) : ℕ :=
  ⌈logTwo (logTwo (2 * (d : ℝ)))⌉₊

noncomputable def testPolynomial (g : Polynomial ℤ) (d : ℕ) (m r : ℤ) : Polynomial ℤ :=
  graeffe^[graeffeCount d] (g.comp (Polynomial.C m + Polynomial.C r * Polynomial.X))

noncomputable def testEmpty (g : Polynomial ℤ) (d : ℕ) (m r : ℤ) : Bool :=
  let q := testPolynomial g d m r
  decide ((∑ j ∈ Finset.range q.natDegree, |q.coeff (j + 1)|) < |q.coeff 0|)

/-- Fuel counts remaining halvings. At fuel zero the scale is one on valid inputs. -/
noncomputable def searchScales (g : Polynomial ℤ) (d : ℕ) : ℕ → ℕ → List ℤ → List ℤ
  | 0, h, centers =>
    let kept := centers.filter fun m => !(testEmpty g d m ((h : ℤ) + 2))
    (kept.flatMap fun m => [m - 1, m, m + 1]).eraseDups
  | fuel + 1, h, centers =>
    let kept := centers.filter fun m => !(testEmpty g d m ((h : ℤ) + 2))
    searchScales g d fuel (h / 2)
      (kept.flatMap fun m => [m - (h / 2 : ℕ), m + (h / 2 : ℕ)])

noncomputable def searchCandidates (f : Polynomial ℤ) (n b : ℕ) : List ℤ :=
  searchScales (truncate f n b) (min n b) b (2 ^ b) [0]

noncomputable def elementaryOutput (f : Polynomial ℤ) (n b : ℕ) : List ℤ :=
  exactZeros f ([-1, 0, 1] ++ searchCandidates f n b)

end IntegerRootsFN.Main


