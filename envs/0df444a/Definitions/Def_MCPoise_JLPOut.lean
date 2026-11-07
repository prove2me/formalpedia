-- Prove2me | Definitions.Def_MCPoise_JLPOut
-- name    : MCPoise_JLPOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:09.696787+00:00
-- url     : https://prove2.me/theorems/cf8974c8-6886-4312-b1f9-7c214dc42c30
-- title:
--   A sparse rational solution of Junction-LP and its encoding
-- statement:
--   A solution of Junction-LP as an algorithm outputs it: four lists of entries, for the variables $x_e$, $x_{e,j}$, $\lambda_{i,j}$ and $f_p$, with rational values. A variable with no entry is $0$ and repeated entries add. The number of entries is the support size in Lemma 2.1.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.1, p.10

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_encIn
import Definitions.Def_OnlineCRS_Combine_encRat

namespace MCPoise

open OnlineCRS.Combine

/-- **A rational, sparse solution of Junction-LP, as a machine outputs it.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.1, p.10: "a feasible fractional solution with polynomial support size".

`x` has entries `(u, v, x_{uv})`; `x'` entries `(u, v, j, x_{uv,j})`; `lam` entries `(i, j, λ_{i,j})`; `f` entries
`(i, b, j, p, f_p)`, with `p` the vertices of the path, for the label `(i, b, j)` of Junction-LP.

**Formalization Note.** A variable with no entry is `0`, and repeated entries add. -/
structure JLPOut where
  x : List (ℕ × ℕ × ℚ)
  x' : List (ℕ × ℕ × ℕ × ℚ)
  lam : List (ℕ × ℕ × ℚ)
  f : List (ℕ × Bool × ℕ × List ℕ × ℚ)

/-- The value of `x_e` read from the output. -/
noncomputable def JLPOut.xVal (o : JLPOut) {n : ℕ} (e : Sym2 (Fin n)) : ℝ :=
  ((o.x.filter fun a => s(a.1, a.2.1) = e.map Fin.val).map fun a => (a.2.2 : ℝ)).sum

/-- The value of `x_{e,j}` read from the output. -/
noncomputable def JLPOut.x'Val (o : JLPOut) {n k : ℕ} (e : Sym2 (Fin n)) (j : Fin k) : ℝ :=
  ((o.x'.filter fun a => s(a.1, a.2.1) = e.map Fin.val ∧ a.2.2.1 = j.val).map
    fun a => (a.2.2.2 : ℝ)).sum

/-- The value of `λ_{i,j}` read from the output. -/
noncomputable def JLPOut.lamVal (o : JLPOut) {k : ℕ} (i j : Fin k) : ℝ :=
  ((o.lam.filter fun a => a.1 = i.val ∧ a.2.1 = j.val).map fun a => (a.2.2 : ℝ)).sum

/-- The value of `f_p` for the label `(i, b, j)` read from the output. -/
noncomputable def JLPOut.fVal (o : JLPOut) {n k : ℕ} (i : Fin k) (b : Bool) (j : Fin k)
    (p : List (Fin n)) : ℝ :=
  ((o.f.filter fun a => a.1 = i.val ∧ a.2.1 = b ∧ a.2.2.1 = j.val ∧
      a.2.2.2.1 = p.map Fin.val).map fun a => (a.2.2.2.2 : ℝ)).sum

/-- The words of a list of numbers: its length first, then the numbers in binary. -/
def tokNats (l : List ℕ) : List (List Sym) :=
  ReserveLB.tokList (fun a => [encNat a]) l

/-- **Encoding of the output of Lemma 2.1.** The four lists in order, each length-prefixed, numbers and rationals in
binary. Injective (`Solutions/verification/MCPoise_sanity.lean`). -/
def encJLPOut (o : JLPOut) : List Sym :=
  EulerSparsify.joinW
    (ReserveLB.tokList (fun a : ℕ × ℕ × ℚ => [encNat a.1, encNat a.2.1, encRat a.2.2]) o.x ++
      ReserveLB.tokList (fun a : ℕ × ℕ × ℕ × ℚ =>
        [encNat a.1, encNat a.2.1, encNat a.2.2.1, encRat a.2.2.2]) o.x' ++
      ReserveLB.tokList (fun a : ℕ × ℕ × ℚ => [encNat a.1, encNat a.2.1, encRat a.2.2]) o.lam ++
      ReserveLB.tokList (fun a : ℕ × Bool × ℕ × List ℕ × ℚ =>
        [encNat a.1, encNat (if a.2.1 then 1 else 0), encNat a.2.2.1] ++ tokNats a.2.2.2.1 ++
          [encRat a.2.2.2.2]) o.f)

end MCPoise


