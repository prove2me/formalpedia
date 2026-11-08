-- Prove2me | Definitions.Def_KelnerLinSolve_FloatInstance
-- name    : KelnerLinSolve_FloatInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:43.864375+00:00
-- url     : https://prove2.me/theorems/7728a854-1c4b-415e-af64-4d8765535e26
-- title:
--   Floating-point instances of Theorem 1.1, the input and output words, and the normalization exponents $\alpha,\beta$
-- statement:
--   A floating-point number is $u2^e$ with $u,e\in\mathbb Z$. An instance consists of the dimension $n$; the nonzero entries of $A\in\mathbb R^{n\times n}$ as a list of $(i, j, u, e)$ with $A_{ij} = u2^e$, in any order; the right-hand side $b\in\mathbb R^n$ as a vector of pairs $(u,e)$ with $b_i = u2^e$, zero entries included; and the accuracy exponent $E$ of $\varepsilon = 2^{-E}$. It is well formed if the listed positions are distinct and every listed significand is nonzero; then $m$, the length of the list, is the number of nonzero entries of $A$.
--
--   The **input word** lists $n$, $E$, $m$, then $i\#j\#u\#e$ for each entry, then $u\#e$ for each $b_i$, in binary and signed binary. It contains no condition-number bound and no bounds $B_{\mathrm{sig}}, B_{\mathrm{exp}}$. The **output word** is $q_1\#\cdots\#q_n\#\gamma$.
--
--   The normalization exponents are
--
--   $$
--   \alpha = \max_{A_{ij}=u2^e\neq0} (e + \mathrm{len}(u)), \qquad \beta = \max_{b_i = u2^e,\ u\ne0} (e + \mathrm{len}(u)) .
--   $$
--
--   **Formalization Note** $\alpha$ and $\beta$ are list maxima, set to $0$ on an empty list; that value is never used, since the statements about them assume $A\neq0$ and $b\neq0$. Indices are $0$-based.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §1.1, p.3; Theorem 1.1, p.3; §4.1, p.12

import Mathlib
import Definitions.Def_KelnerLinSolve_encInt

namespace KelnerLinSolve

/-- The value `u 2^e` of a floating-point number with integer significand `u` and integer exponent
`e` (Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission
(sha256 d1af55cb…), §1.1, p.3). -/
noncomputable def floatVal (u e : ℤ) : ℝ := (u : ℝ) * (2 : ℝ) ^ e

/-- **A floating-point instance of Theorem 1.1** (Kelner, sha256 d1af55cb…, §1.1, p.3): the dimension
`n`; "the matrix is supplied as a list of its nonzero entries and their row and column indices"
(`entries`, with each entry `(i, j, u, e)` standing for `A_{ij} = u 2^e`, in any order); "the
right-hand side is supplied as a vector of encoded entries" (`rhs i = (u, e)` for `bᵢ = u 2^e`, zero
entries included); and the accuracy exponent `E` of `ε = 2^{−E}`. -/
structure FloatInstance where
  n : ℕ
  entries : List (Fin n × Fin n × ℤ × ℤ)
  rhs : Fin n → ℤ × ℤ
  E : ℕ

namespace FloatInstance

/-- The entry list lists distinct positions, each with a nonzero significand (so it lists exactly
the nonzero entries of `A`). -/
def WellFormed (I : FloatInstance) : Prop :=
  (I.entries.map fun t => (t.1, t.2.1)).Nodup ∧ ∀ t ∈ I.entries, t.2.2.1 ≠ 0

/-- The real matrix `A`: `u 2^e` at a listed position `(i, j, u, e)`, `0` elsewhere. -/
noncomputable def A (I : FloatInstance) : Matrix (Fin I.n) (Fin I.n) ℝ := fun i j =>
  ((I.entries.filter fun t => t.1 == i && t.2.1 == j).map fun t => floatVal t.2.2.1 t.2.2.2).sum

/-- The real right-hand side `bᵢ = u 2^e` for `rhs i = (u, e)`. -/
noncomputable def b (I : FloatInstance) : Fin I.n → ℝ := fun i => floatVal (I.rhs i).1 (I.rhs i).2

/-- The number `m` of listed entries (for a well-formed instance, the number of nonzero entries
of `A`). -/
def m (I : FloatInstance) : ℕ := I.entries.length

/-- **The input word.** `n # E # m # i₁ # j₁ # u₁ # e₁ # ⋯ # i_m # j_m # u_m # e_m # u'₁ # e'₁ # ⋯ #
u'ₙ # e'ₙ`: `n`, `E`, `m` and the `0`-based indices in binary (`encNat`), significands and exponents
in signed binary (`encInt`, exactly `bits(w)` symbols). It contains no condition-number bound and no
`B_sig`, `B_exp`: the machine reads only the data (Theorem 1.1, p.3: "The algorithm does not require
a supplied condition-number bound"). -/
def encInst (I : FloatInstance) : List (Option Bool) :=
  IntMul.joinSep ([encNat I.n, encNat I.E, encNat I.entries.length]
    ++ (I.entries.flatMap fun t => [encNat t.1, encNat t.2.1, encInt t.2.2.1, encInt t.2.2.2])
    ++ ((List.finRange I.n).flatMap fun i => [encInt (I.rhs i).1, encInt (I.rhs i).2]))

/-- `α`, the maximum of `e + len(u)` over the listed (nonzero) entries `u 2^e` of `A` (Kelner,
sha256 d1af55cb…, §4.1, p.12).

**Formalization Note.** The maximum of the list; `0` when the list is empty (never used: every
statement about `α` assumes `A ≠ 0`). -/
def alphaExp (I : FloatInstance) : ℤ :=
  ((I.entries.map fun (t : Fin I.n × Fin I.n × ℤ × ℤ) => t.2.2.2 + (lenInt t.2.2.1 : ℤ)).max?).getD 0

/-- `β`, the maximum of `e + len(u)` over the nonzero entries `u 2^e` (`u ≠ 0`) of `b` (Kelner,
sha256 d1af55cb…, §4.1, p.12).

**Formalization Note.** `0` when every `u` is zero (never used: every statement about `β` assumes
`b ≠ 0`). -/
def betaExp (I : FloatInstance) : ℤ :=
  ((((List.finRange I.n).filter fun i => (I.rhs i).1 != 0).map
    fun i => (I.rhs i).2 + (lenInt (I.rhs i).1 : ℤ)).max?).getD 0

end FloatInstance

/-- **The output word** `q₁ # ⋯ # qₙ # γ` of Theorem 1.1 (Kelner, sha256 d1af55cb…, p.3: "returns
integers `q₁, …, qₙ, γ`"), each integer in signed binary. -/
def encOutput {n : ℕ} (q : Fin n → ℤ) (γ : ℤ) : List (Option Bool) :=
  IntMul.joinSep ((List.finRange n).map (fun i => encInt (q i)) ++ [encInt γ])

end KelnerLinSolve


