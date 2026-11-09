-- Prove2me | Definitions.Def_GoodQLTC_IsPolyTimeInBlocklength
-- name    : GoodQLTC_IsPolyTimeInBlocklength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:39:23.672416+00:00
-- url     : https://prove2.me/theorems/b49ccdaf-2ee6-4d05-bbf3-27e95d47195d
-- title:
--   Construction in time polynomial in the blocklength
-- statement:
--   A family of CSS codes $\nu\mapsto(H_X^\nu,H_Z^\nu)$ with blocklengths $N_\nu$ is **constructible in time polynomial in $N_\nu$** if there are one Turing machine $M$ and one polynomial $p$ such that, on input $\nu$, $M$ outputs an encoding of $(N_\nu,m_X,m_Z,H_X^\nu,H_Z^\nu)$ within $p(N_\nu)$ steps.
--
--   This is the paper's notion of an explicit family (Lemma 14.2: "its input is the quotient level $\nu$").
--
--   **Formalization Note** Mathlib's `Turing.TM2ComputableInTime` with input $\nu$ in unary; the time function is evaluated at the input length and must be at most $p(N_\nu)$. The output encoding `encodeCSS` writes the three numbers in unary and the rows bit by bit; it is injective (proved in the sanity file) and of linear length.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Main Theorem, p.3 (PDF p.6); Lemma 14.2, p.56 (PDF p.59)

import Mathlib

namespace GoodQLTC

/-- The output of the construction of a CSS code: `(N, m_X, m_Z, rows of H_X, rows of H_Z)`, each
row a list of `N` bits (`true` = entry `1`). -/
abbrev CSSData : Type := ℕ × ℕ × ℕ × List (List Bool) × List (List Bool)

/-- The rows of a binary matrix `M ∈ F_2^{a × b}` as lists of bits, in index order. -/
def rowsOf {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 2)) : List (List Bool) :=
  List.ofFn fun i => List.ofFn fun j => decide (M i j = 1)

/-- The data `(N, m_X, m_Z, rows H_X, rows H_Z)` of a CSS code with `Fin`-indexed check matrices. -/
def cssData {N mX mZ : ℕ} (HX : Matrix (Fin mX) (Fin N) (ZMod 2))
    (HZ : Matrix (Fin mZ) (Fin N) (ZMod 2)) : CSSData :=
  (N, mX, mZ, rowsOf HX, rowsOf HZ)

/-- A list of rows written as one word: each row is preceded by the separator `none` and its bits
are written as `some b`. -/
def encodeRows (R : List (List Bool)) : List (Option Bool) :=
  R.flatMap fun r => none :: r.map some

/-- The output **encoding** of `(N, m_X, m_Z, H_X, H_Z)` as a word over a finite alphabet: the three
numbers in unary and the two row lists by `encodeRows`, each field written in its own letters
(`Sum` tags). Its length is linear in `N + m_X + m_Z + N(m_X + m_Z)` (dense output). -/
def encodeCSS (x : CSSData) : List (Bool ⊕ Bool ⊕ Bool ⊕ Option Bool ⊕ Option Bool) :=
  (Computability.unaryEncodeNat x.1).map Sum.inl ++
    (Computability.unaryEncodeNat x.2.1).map (Sum.inr ∘ Sum.inl) ++
    (Computability.unaryEncodeNat x.2.2.1).map (Sum.inr ∘ Sum.inr ∘ Sum.inl) ++
    (encodeRows x.2.2.2.1).map (Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) ++
    (encodeRows x.2.2.2.2).map (Sum.inr ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr)

/-- **Construction in time polynomial in the blocklength**, Gay–Jeronimo, arXiv:2609.20780 (held
version), Main Theorem, p.3 ("The check matrices can be constructed in time polynomial in `N_ν`")
and Lemma 14.2, p.56 ("its input is the quotient level `ν`").

For a family `ν ↦ D ν` of CSS data with blocklengths `N ν`, there is **one** multi-stack Turing
machine (Mathlib's `Turing.TM2ComputableInTime`) that, on input `ν` written in unary, outputs
`encodeCSS (D ν)`, together with **one** polynomial `p` such that on input `ν` it halts within
`p(N ν)` steps.

**Formalization Note.** The time function of `TM2ComputableInTime` is evaluated at the input length
(`= ν` in unary), and the bound required is `p(N_ν)`, polynomial in the blocklength, not in the
input length (`ν = O(log N_ν)`, proof of Lemma 14.2, p.57). The output encoding `encodeCSS` is
injective and of linear length. -/
def IsPolyTimeInBlocklength (N : ℕ → ℕ) (D : ℕ → CSSData) : Prop :=
  ∃ (M : Turing.TM2ComputableInTime Computability.unaryEncodingNat.encode encodeCSS D)
    (p : Polynomial ℕ), ∀ ν, M.time (Computability.unaryEncodingNat.encode ν).length ≤ p.eval (N ν)

end GoodQLTC


