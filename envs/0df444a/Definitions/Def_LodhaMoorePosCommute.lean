-- Prove2me | Definitions.Def_LodhaMoorePosCommute
-- name    : LodhaMoorePosCommute
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-02T19:09:14.624528+00:00
-- url     : https://prove2.me/theorems/4c79d492-000b-43d7-85a2-6e38b1d570d9
-- title:
--   Lodha–Moore p. 9 — the substitutions with commutation of positive letters only
-- statement:
--   `LodhaMoorePosCommute.Step` is the one-step substitution relation on words in the generators $x_s$, $y_s$ ($s$ a finite binary sequence) of the Lodha–Moore mission's `LodhaMoore.Step`, with one change: the commutation substitution applies only to letters with positive exponents.
--
--   Lodha and Moore write on p. 9: "In what follows, we will say that an $S$-word $\Omega_1$ is *derived from* an $S$-word $\Omega_0$ if it is the result of applying substitutions of the following forms: $y_t^i x_s^{\pm1} \Rightarrow x_s^{\pm1} y^i_{t.x_s^{\pm1}}$, $y_s \Rightarrow x_s y_{s0} y_{s10}^{-1} y_{s11}$, $y_u y_v \Leftrightarrow y_v y_u$, $x^{i+j} \Leftrightarrow x^i x^j$, $y^{i+j} \Leftrightarrow y^i y^j$, delete an occurrence of $y^i y^{-i}$, where $s, t, u, v \in 2^{<\mathbb N}$ are such that $t.x_s$ is defined and $u$ and $v$ are incompatible, and $i, j$ are nonzero integers of the same sign."
--
--   `LodhaMoore.Step` reads the commutation $y_u y_v \Leftrightarrow y_v y_u$ with arbitrary exponents $y_u^i y_v^j \Leftrightarrow y_v^j y_u^i$, and it adds the expansion $y_s^{-1} \Rightarrow x_s^{-1} y_{s00}^{-1} y_{s01} y_{s1}^{-1}$ that the proofs of Lemmas 5.2 and 5.6 use (pp. 10–11). `LodhaMoorePosCommute.Step` keeps all of these rules but allows $y_u^i y_v^j \Leftrightarrow y_v^j y_u^i$ (for incompatible $u$, $v$) only when $i > 0$ and $j > 0$. This includes the printed rule read with exponent $1$. A $y$-letter with a negative exponent then commutes with no other $y$-letter (it still moves past an $x_s$ by the first substitution).
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 9, the substitutions defining derivations, with yᵤyᵥ ⇔ yᵥyᵤ read for positive exponents

import Definitions.Def_LodhaMooreWords

/-!
# Lodha–Moore p. 9: the substitutions with commutation of positive letters only

Y. Lodha and J. T. Moore, arXiv:1308.4250v3, p. 9: the substitutions defining derivations, with the
rule `y_u y_v ⇔ y_v y_u` taken for positive exponents only.
-/

namespace LodhaMoorePosCommute

open LodhaMoore

/-- The substitutions of p. 9 (as in `LodhaMoore.Step`), with `y_u^i y_v^j ⇔ y_v^j y_u^i` only for
`i, j > 0`. -/
inductive Step : Word → Word → Prop
  | moveX (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFin s t = some t') :
      Step (pre ++ [(.y t, i), (.x s, 1)] ++ post) (pre ++ [(.x s, 1), (.y t', i)] ++ post)
  | moveXInv (pre post : Word) (s t t' : Seq) (i : ℤ) (h : xFinInv s t = some t') :
      Step (pre ++ [(.y t, i), (.x s, -1)] ++ post) (pre ++ [(.x s, -1), (.y t', i)] ++ post)
  | expand (pre post : Word) (s : Seq) :
      Step (pre ++ [(.y s, 1)] ++ post)
        (pre ++ [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
          (.y (s ++ [true, true]), 1)] ++ post)
  | expandInv (pre post : Word) (s : Seq) :
      Step (pre ++ [(.y s, -1)] ++ post)
        (pre ++ [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
          (.y (s ++ [true]), -1)] ++ post)
  | commute (pre post : Word) (u v : Seq) (i j : ℤ) (hi : 0 < i) (hj : 0 < j)
      (h : Incompatible u v) :
      Step (pre ++ [(.y u, i), (.y v, j)] ++ post) (pre ++ [(.y v, j), (.y u, i)] ++ post)
  | split (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      Step (pre ++ [(g, i + j)] ++ post) (pre ++ [(g, i), (g, j)] ++ post)
  | merge (pre post : Word) (g : Gen) (i j : ℤ) (hi : i ≠ 0) (hj : j ≠ 0) (hij : 0 < i * j) :
      Step (pre ++ [(g, i), (g, j)] ++ post) (pre ++ [(g, i + j)] ++ post)
  | cancel (pre post : Word) (s : Seq) (i : ℤ) (hi : i ≠ 0) :
      Step (pre ++ [(.y s, i), (.y s, -i)] ++ post) (pre ++ post)

end LodhaMoorePosCommute


