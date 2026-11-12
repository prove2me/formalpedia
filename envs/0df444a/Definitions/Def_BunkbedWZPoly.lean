-- Prove2me | Definitions.Def_BunkbedWZPoly
-- name    : BunkbedWZPoly
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-12T00:06:44.615375+00:00
-- url     : https://prove2.me/theorems/7b9f2793-1ed8-4882-9f5a-68b9f228cfb5
-- title:
--   The Wierman--Ziff difference polynomial for Hollom's hypergraph
-- statement:
--   In the Wierman--Ziff five-state model, each hyperedge of a $3$-uniform hypergraph independently takes one of five states on each of the two levels of the bunkbed, the state recording which of the three vertices the hyperedge connects. Writing $x = P_{abc}$, $y = P_{a|b|c}$, $z = P_{a|bc}$, $u = P_{ab|c}$ and $v = P_{ac|b}$ for the five state probabilities, a connection probability on Hollom's hypergraph is a sum over $5^{12}$ configurations, hence a polynomial of degree $12$ in these five quantities.
--
--   This file records, explicitly, the **difference** between the cross-level and the same-level connection probability for Hollom's hypergraph in the symmetric case $u = v$:
--
--   $$\texttt{wzDiffPoly}(x,y,z,u) \;=\; \mathbb{P}^{\mathrm{wz}}\bigl[u_1 \leftrightarrow u_{10}'\bigr] - \mathbb{P}^{\mathrm{wz}}\bigl[u_1 \leftrightarrow u_{10}\bigr].$$
--
--   It is homogeneous of degree $12$, with $231$ monomials when fully expanded.
--
--   Rather than listing those monomials, the polynomial is presented in a **graded form** which makes the robustness estimate of Lemma 3.3 transparent. Put
--   $$W \;=\; \texttt{wzDet}(x,y,u) \;=\; xy - u^2,$$
--   the determinant-like quantity appearing in Eq. [1] of Gladkov--Pak--Zimin. Then the coefficient of $z^j$ in the difference is divisible by exactly $W^{6-j}$ for $0 \le j \le 6$, where $6$ is the number of hyperedges of Hollom's hypergraph, and $\texttt{wzR}j$ is the resulting cofactor, homogeneous of degree $j$ in $x, y, u$. For $j \ge 7$ no factor of $W$ remains and $\texttt{wzR}j$ is the full coefficient, of degree $12 - j$.
--
--   Two features of this presentation deserve comment.
--
--   First, the $z$-free term is exactly $W^6$, with cofactor $\texttt{wzR}0 = 1$. This is not an accident: the configurations contributing to it are precisely those in which every hyperedge is fully present on one level and fully absent on the other, which is exactly the *alternative* bunkbed hypergraph model. Each such configuration carries weight $W^6$, there are $2^6 = 64$ of them, and by Hollom's computation (Lemma 3.1) their net contribution to the difference is $13 - 12 = 1$.
--
--   Second, the grading is what makes the hypothesis $400\,P_{a|bc} \le P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$ of Eq. [1] do its work. That hypothesis reads $400 z \le W$, so the $z^j$ term is of size $O(W^6/400^j)$ relative to the leading term; every correction is therefore small compared with $W^6$, and the difference is positive whenever $W > 0$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3 (pp. 3-6); the quantity W is the right-hand side of Eq. [1] on p. 3, and the z-free term reflects Lemma 3.1 (12/64 vs 13/64).

import Definitions.Def_BunkbedHypergraph

/-!
# The WZ difference polynomial for Hollom's hypergraph

Section 3 of Gladkov-Pak-Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) e2420725122.

`wzProb` is a sum over `5 ^ 12` state configurations, so each connection probability is a
polynomial of degree 12 in the five WZ state probabilities. In the symmetric case
`P_ab|c = P_ac|b` the difference between the cross-level and the same-level probability is a
polynomial in the four remaining quantities, and this file records it explicitly.

It is written in the *graded* form that makes the robustness estimate of Lemma 3.3 transparent.
Put `W = P_abc * P_a|b|c - P_ab|c * P_ac|b` (the determinant-like quantity of Eq. [1]) and
`z = P_a|bc`. Then the coefficient of `z ^ j` is divisible by exactly `W ^ (6 - j)` for `j` up to
`6`, where `6` is the number of hyperedges of Hollom's hypergraph, and `R_j` below is the
resulting cofactor, homogeneous of degree `j` in `x`, `y`, `u`.

The `z`-free term is exactly `W ^ 6`. Those are the configurations in which every hyperedge is
fully present on one level and fully absent on the other -- which is precisely the *alternative*
model of Lemma 3.1 -- and they contribute `13 - 12 = 1` per unit of weight.

Since `z` is bounded by `W / 400` under Eq. [1], every `j >= 1` term is `O(W ^ 6 / 400 ^ j)`, so
the `z`-free term dominates and the difference is positive. That is the content of Lemma 3.3.
-/

namespace Bunkbed.Hyper

/-- `wzDet x y u = x * y - u ^ 2`, the determinant-like quantity of Eq. [1] of
Gladkov-Pak-Zimin, specialised to the symmetric case `P_ab|c = P_ac|b = u`. -/
def wzDet (x y u : Rat) : Rat := x * y - u * u

/-- The degree-1 form `R_1`: the cofactor of `z ^ 1` after dividing by `W ^ 5`. -/
def wzR1 (x y u : Rat) : Rat :=
      (-8 : Rat) * u + (-4 : Rat) * y + (2 : Rat) * x

/-- The degree-2 form `R_2`: the cofactor of `z ^ 2` after dividing by `W ^ 4`. -/
def wzR2 (x y u : Rat) : Rat :=
      (-5 : Rat) * u ^ 2 + (-8 : Rat) * y * u + (-2 : Rat) * y ^ 2 + (-50 : Rat) * x * u
      + (-28 : Rat) * x * y + (-8 : Rat) * x ^ 2

/-- The degree-3 form `R_3`: the cofactor of `z ^ 3` after dividing by `W ^ 3`. -/
def wzR3 (x y u : Rat) : Rat :=
      (-44 : Rat) * u ^ 3 + (-86 : Rat) * y * u ^ 2 + (-48 : Rat) * y ^ 2 * u + (-8 : Rat) * y ^ 3
      + (-76 : Rat) * x * u ^ 2 + (-124 : Rat) * x * y * u + (-36 : Rat) * x * y ^ 2
      + (-140 : Rat) * x ^ 2 * u + (-98 : Rat) * x ^ 2 * y + (-32 : Rat) * x ^ 3

/-- The degree-4 form `R_4`: the cofactor of `z ^ 4` after dividing by `W ^ 2`. -/
def wzR4 (x y u : Rat) : Rat :=
      (-90 : Rat) * u ^ 4 + (-276 : Rat) * y * u ^ 3 + (-261 : Rat) * y ^ 2 * u ^ 2
      + (-96 : Rat) * y ^ 3 * u + (-12 : Rat) * y ^ 4 + (-362 : Rat) * x * u ^ 3
      + (-829 : Rat) * x * y * u ^ 2 + (-522 : Rat) * x * y ^ 2 * u + (-96 : Rat) * x * y ^ 3
      + (-368 : Rat) * x ^ 2 * u ^ 2 + (-662 : Rat) * x ^ 2 * y * u + (-219 : Rat) * x ^ 2 * y ^ 2
      + (-242 : Rat) * x ^ 3 * u + (-225 : Rat) * x ^ 3 * y + (-45 : Rat) * x ^ 4

/-- The degree-5 form `R_5`: the cofactor of `z ^ 5` after dividing by `W ^ 1`. -/
def wzR5 (x y u : Rat) : Rat :=
      (130 : Rat) * u ^ 5 + (65 : Rat) * y * u ^ 4 + (-192 : Rat) * y ^ 2 * u ^ 3
      + (-192 : Rat) * y ^ 3 * u ^ 2 + (-60 : Rat) * y ^ 4 * u + (-6 : Rat) * y ^ 5
      + (-42 : Rat) * x * u ^ 4 + (-1096 : Rat) * x * y * u ^ 3 + (-1587 : Rat) * x * y ^ 2 * u ^ 2
      + (-720 : Rat) * x * y ^ 3 * u + (-102 : Rat) * x * y ^ 4 + (-674 : Rat) * x ^ 2 * u ^ 3
      + (-2417 : Rat) * x ^ 2 * y * u ^ 2 + (-1950 : Rat) * x ^ 2 * y ^ 2 * u + (-420 : Rat) * x ^ 2 * y ^ 3
      + (-652 : Rat) * x ^ 3 * u ^ 2 + (-1494 : Rat) * x ^ 3 * y * u + (-607 : Rat) * x ^ 3 * y ^ 2
      + (-264 : Rat) * x ^ 4 * u + (-320 : Rat) * x ^ 4 * y + (-34 : Rat) * x ^ 5

/-- The degree-6 form `R_6`: the cofactor of `z ^ 6` after dividing by `W ^ 0`. -/
def wzR6 (x y u : Rat) : Rat :=
      (136 : Rat) * u ^ 6 + (476 : Rat) * y * u ^ 5 + (407 : Rat) * y ^ 2 * u ^ 4
      + (80 : Rat) * y ^ 3 * u ^ 3 + (-30 : Rat) * y ^ 4 * u ^ 2 + (-12 : Rat) * y ^ 5 * u
      + (-1 : Rat) * y ^ 6 + (880 : Rat) * x * u ^ 5 + (1492 : Rat) * x * y * u ^ 4
      + (-22 : Rat) * x * y ^ 2 * u ^ 3 + (-835 : Rat) * x * y ^ 3 * u ^ 2 + (-360 : Rat) * x * y ^ 4 * u
      + (-42 : Rat) * x * y ^ 5 + (1079 : Rat) * x ^ 2 * u ^ 4 + (-316 : Rat) * x ^ 2 * y * u ^ 3
      + (-3129 : Rat) * x ^ 2 * y ^ 2 * u ^ 2 + (-2030 : Rat) * x ^ 2 * y ^ 3 * u
      + (-345 : Rat) * x ^ 2 * y ^ 4 + (220 : Rat) * x ^ 3 * u ^ 3 + (-2388 : Rat) * x ^ 3 * y * u ^ 2
      + (-3244 : Rat) * x ^ 3 * y ^ 2 * u + (-895 : Rat) * x ^ 3 * y ^ 3 + (-179 : Rat) * x ^ 4 * u ^ 2
      + (-1380 : Rat) * x ^ 4 * y * u + (-829 : Rat) * x ^ 4 * y ^ 2 + (-82 : Rat) * x ^ 5 * u
      + (-222 : Rat) * x ^ 5 * y + (-8 : Rat) * x ^ 6

/-- The degree-5 form `R_7`: the cofactor of `z ^ 7`. -/
def wzR7 (x y u : Rat) : Rat :=
      (196 : Rat) * u ^ 5 + (202 : Rat) * y * u ^ 4 + (-114 : Rat) * y ^ 2 * u ^ 3
      + (-179 : Rat) * y ^ 3 * u ^ 2 + (-60 : Rat) * y ^ 4 * u + (-6 : Rat) * y ^ 5
      + (338 : Rat) * x * u ^ 4 + (-800 : Rat) * x * y * u ^ 3 + (-1704 : Rat) * x * y ^ 2 * u ^ 2
      + (-838 : Rat) * x * y ^ 3 * u + (-120 : Rat) * x * y ^ 4 + (-432 : Rat) * x ^ 2 * u ^ 3
      + (-3044 : Rat) * x ^ 2 * y * u ^ 2 + (-2706 : Rat) * x ^ 2 * y ^ 2 * u + (-599 : Rat) * x ^ 2 * y ^ 3
      + (-862 : Rat) * x ^ 3 * u ^ 2 + (-2400 : Rat) * x ^ 3 * y * u + (-996 : Rat) * x ^ 3 * y ^ 2
      + (-380 : Rat) * x ^ 4 * u + (-520 : Rat) * x ^ 4 * y + (-48 : Rat) * x ^ 5

/-- The degree-4 form `R_8`: the cofactor of `z ^ 8`. -/
def wzR8 (x y u : Rat) : Rat :=
      (2 : Rat) * u ^ 4 + (-224 : Rat) * y * u ^ 3 + (-296 : Rat) * y ^ 2 * u ^ 2
      + (-120 : Rat) * y ^ 3 * u + (-15 : Rat) * y ^ 4 + (-420 : Rat) * x * u ^ 3
      + (-1366 : Rat) * x * y * u ^ 2 + (-952 : Rat) * x * y ^ 2 * u + (-180 : Rat) * x * y ^ 3
      + (-949 : Rat) * x ^ 2 * u ^ 2 + (-1700 : Rat) * x ^ 2 * y * u + (-566 : Rat) * x ^ 2 * y ^ 2
      + (-606 : Rat) * x ^ 3 * u + (-546 : Rat) * x ^ 3 * y + (-108 : Rat) * x ^ 4

/-- The degree-3 form `R_9`: the cofactor of `z ^ 9`. -/
def wzR9 (x y u : Rat) : Rat :=
      (-88 : Rat) * u ^ 3 + (-204 : Rat) * y * u ^ 2 + (-120 : Rat) * y ^ 2 * u + (-20 : Rat) * y ^ 3
      + (-378 : Rat) * x * u ^ 2 + (-528 : Rat) * x * y * u + (-150 : Rat) * x * y ^ 2
      + (-396 : Rat) * x ^ 2 * u + (-276 : Rat) * x ^ 2 * y + (-112 : Rat) * x ^ 3

/-- The degree-2 form `R_10`: the cofactor of `z ^ 10`. -/
def wzR10 (x y u : Rat) : Rat :=
      (-51 : Rat) * u ^ 2 + (-60 : Rat) * y * u + (-15 : Rat) * y ^ 2 + (-114 : Rat) * x * u
      + (-66 : Rat) * x * y + (-54 : Rat) * x ^ 2

/-- The degree-1 form `R_11`: the cofactor of `z ^ 11`. -/
def wzR11 (x y u : Rat) : Rat :=
      (-12 : Rat) * u + (-6 : Rat) * y + (-12 : Rat) * x

/-- The degree-0 form `R_12`: the cofactor of `z ^ 12`. -/
def wzR12 (_x _y _u : Rat) : Rat :=
      (-1 : Rat)

/-- The difference `Pwz[u1 <-> u10-prime] - Pwz[u1 <-> u10]` for Hollom's hypergraph, as an
explicit polynomial in `x = P_abc`, `y = P_a|b|c`, `z = P_a|bc` and `u = P_ab|c = P_ac|b`.
Homogeneous of degree 12, with 231 monomials when fully expanded. -/
def wzDiffPoly (x y z u : Rat) : Rat :=
  wzDet x y u ^ 6
    + z * wzDet x y u ^ 5 * wzR1 x y u
    + z ^ 2 * wzDet x y u ^ 4 * wzR2 x y u
    + z ^ 3 * wzDet x y u ^ 3 * wzR3 x y u
    + z ^ 4 * wzDet x y u ^ 2 * wzR4 x y u
    + z ^ 5 * wzDet x y u * wzR5 x y u
    + z ^ 6 * wzR6 x y u
    + z ^ 7 * wzR7 x y u
    + z ^ 8 * wzR8 x y u
    + z ^ 9 * wzR9 x y u
    + z ^ 10 * wzR10 x y u
    + z ^ 11 * wzR11 x y u
    + z ^ 12 * wzR12 x y u

end Bunkbed.Hyper


