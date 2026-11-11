-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_PolyTime
-- name    : CorrBoundsPoly_ExactDegree_PolyTime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:59:40.407968+00:00
-- url     : https://prove2.me/theorems/38ce7cc2-e3e3-4280-91ed-79c02922b7bb
-- title:
--   Theorem 4.1 (last clause) — evaluation maps of $F_s$ and $H_{n,d}$ on bit strings, and the unary input encoding
-- statement:
--   To state that the cores are evaluable in polynomial time, the evaluations are viewed as functions on finite strings. The map $\mathrm{evalF}$ sends $(s,x)$, with $s\in\mathbb N$ and a bit string $x$, to $F_s(x)$ when $s\ge1$ and $|x|=M(s)$, and to $0$ otherwise; the map $\mathrm{evalH}$ sends $(d,x)$ to $H_{|x|,d}(x)$ when $d\ge1$ and $|x|\ge M(d+1)$, and to $0$ otherwise. An input $(s,x)$ is written as $s$ in **unary** followed by the bits of $x$, so the input length is $s+|x|$; with $|x|=M(s)\ge s$ (resp. $|x|\ge M(d+1)$) this is the natural size of an instance.
--
--   **Formalization Note** `listToVec m x` reads bit `i` of the list as coordinate `i` (missing bits as `0`; the length is checked first). `evalF`, `evalH : ℕ × List Bool → Bool` output `true` exactly when the polynomial evaluates to `1`. `inputEncoding` is `Computability.encodingProd Computability.unaryEncodingNat (Computability.encodingList Bool)` over the alphabet `Bool ⊕ Bool`; outputs use `Computability.encodingBoolBool`.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), Theorem 4.1, p. 31 (PDF 33); proof of Lemma 4.3, p. 32 (PDF 34)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Cores

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), Theorem 4.1, last clause ("all the cores are evaluable in polynomial time"),
p. 31 (PDF 33); proof of Lemma 4.3, p. 32 (PDF 34).

The evaluation maps of the cores `F_s` and of `H_{n,d}` as functions on bit strings, and the
input encoding used for the polynomial-time claim: the parameter `s` (or `d`) in **unary**, the
input bits as a list, concatenated by Mathlib's `Computability.encodingProd`. -/

/-- A bit list read as a point of `F₂^m` (bit `i` of the list is coordinate `i`; missing bits read
as `0`, which never happens where it is used: the length is checked first). -/
def listToVec (m : ℕ) (x : List Bool) : Fin m → ZMod 2 :=
  fun i => if x.getD i.val false then 1 else 0

/-- `(s, x) ↦ F_s(x)` for `s ≥ 1` and `|x| = M(s)`; `false` on every other input. -/
noncomputable def evalF (p : ℕ × List Bool) : Bool :=
  if 1 ≤ p.1 ∧ p.2.length = M p.1 then
    decide (MvPolynomial.eval (listToVec (M p.1) p.2) (F p.1) = 1)
  else false

/-- `(d, x) ↦ H_{|x|,d}(x)` for `d ≥ 1` and `|x| ≥ M(d+1)`; `false` on every other input. -/
noncomputable def evalH (p : ℕ × List Bool) : Bool :=
  if 1 ≤ p.1 ∧ M (p.1 + 1) ≤ p.2.length then
    decide (MvPolynomial.eval (listToVec p.2.length p.2) (H p.2.length p.1) = 1)
  else false

/-- The input encoding: `s` (or `d`) in unary, then the bits, over the alphabet `Bool ⊕ Bool`. -/
def inputEncoding : Computability.Encoding (ℕ × List Bool) (Bool ⊕ Bool) :=
  Computability.encodingProd Computability.unaryEncodingNat (Computability.encodingList Bool)

end CorrBoundsPoly.ExactDegree


