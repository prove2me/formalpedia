-- Prove2me | Definitions.Def_MarginMaxima_Critical_QaryGadget
-- name    : MarginMaxima_Critical_QaryGadget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:01:49.662486+00:00
-- url     : https://prove2.me/theorems/fe99a196-35dd-4726-8673-026066fcf3bc
-- title:
--   The $q$-ary gadget of §6: representatives of projective points, lines $x+c\beta^\top$ in $\mathbb F_q^{t\times e}$, and the agreement $A(Y)$
-- statement:
--   Let $q$ be a prime power, $t\ge2$, $e\ge1$ integers and $C=\mathbb F_q^{t\times e}$. Let $A$ be a set of representatives of the nonzero $a\in\mathbb F_q^t$ modulo scalars, $L=|A|=(q^t-1)/(q-1)$. The letter of $X\in C$ at $a$ is $a^\top X\in\mathbb F_q^e$. For $x\in C$ and nonzero $\beta\in\mathbb F_q^e$ the **line** is
--   $$B(x,\beta)=\{x+c\beta^\top: c\in\mathbb F_q^t\},$$
--   and the **agreement** of $Y\in C$ with it is $A(Y)=\#\{a\in A: a^\top(Y-x)\in\mathbb F_q\beta\}$.
--
--   The lines are the blocks of the gadget that attains the critical margins (Theorem 3.1(c), (c′)).
--
--   **Formalization Note.** $\mathbb F_q$ is any finite field `F` (with $q$ = `Fintype.card F`). `IsProjReps A` says every element of `A` is nonzero and every nonzero `v` equals `c • a` for a nonzero scalar `c` and exactly one `a ∈ A`. `qLine x β` uses `Matrix.vecMulVec c β` for $c\beta^\top$, and `qAgree A x β Y` counts the `a ∈ A` with `vecMul a (Y - x) = c • β` for some `c`.
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 12–13, §6 (setting, lines, A(Y))

import Mathlib

namespace MarginMaxima.Critical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `A` is a set of representatives of the nonzero vectors of `F^t` modulo nonzero scalars: its
elements are nonzero and every nonzero `v` is a nonzero multiple of exactly one `a ∈ A`. -/
def IsProjReps {t : ℕ} (A : Finset (Fin t → F)) : Prop :=
  (∀ a ∈ A, a ≠ 0) ∧ ∀ v : Fin t → F, v ≠ 0 → ∃! a, a ∈ A ∧ ∃ c : F, c ≠ 0 ∧ v = c • a

/-- The line `B(x, β) = {x + c β^⊤ : c ∈ F^t}` of the `q`-ary gadget in `C = F^{t×e}`. -/
def qLine {t e : ℕ} (x : Matrix (Fin t) (Fin e) F) (β : Fin e → F) :
    Set (Matrix (Fin t) (Fin e) F) :=
  {Y | ∃ c : Fin t → F, Y = x + Matrix.vecMulVec c β}

/-- The agreement `A(Y) = #{a ∈ A : a^⊤ (Y − x) ∈ F_q β}` of `Y` with the line `B(x, β)`; the letter
of `X` at `a` is `a^⊤ X ∈ F^e`. -/
def qAgree {t e : ℕ} (A : Finset (Fin t → F)) (x : Matrix (Fin t) (Fin e) F) (β : Fin e → F)
    (Y : Matrix (Fin t) (Fin e) F) : ℕ :=
  (A.filter fun a => ∃ c : F, Matrix.vecMul a (Y - x) = c • β).card

end MarginMaxima.Critical


