-- Prove2me | Definitions.Def_AutoformalisationSCI_Poly
-- name    : AutoformalisationSCI_Poly
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T15:21:02.419067+00:00
-- url     : https://prove2.me/theorems/774e4bd8-97da-432f-beb8-7b2d9dc2566d
-- title:
--   Polynomial enumerations and the presupposition-resolution sets d, d_l
-- statement:
--   This file formalizes the polynomial constructions at the heart of the paper's lower bounds.
--
--   `cantorPair` is the integer-coefficient pairing $\langle x,y\rangle=(x+y)(x+y+1)+2y$ fixed in the paper (a computable injection $\mathbb N^2\to\mathbb N$). `ComputablePolyEnum m` packages a **computable enumeration of all integer-coefficient polynomials in $m$ variables**: the enumerated polynomials $p_e$, surjectivity, a computable coefficient function (monomials as exponent vectors $\mathrm{Fin}\ m\to\mathbb N$), and a computable bound on total degree. These data are equivalent to computability of the enumeration under a canonical numbering by finite coefficient lists.
--
--   `B k E e n` is the predicate $B_e(n)$ of Eq. (A.3): $p_e(n,x_1,\dots,x_k)\ne0$ for all $(x_1,\dots,x_k)\in\mathbb N^k$; `dSet k E` is $d=\{e:\exists n,\,B_e(n)\}$. `leastWitness` is the partial number $n_e$ of Example 4.1 (the least such $n$, or undefined). `Bgen l k hl E e n` is $B_e^{(l)}(n)$ of Eq. (A.4), built from the alternating quantifier pattern `qtype`/`QuantVec`; `dSetL` is $d_l=\{e:\exists n,\,B_e^{(l)}(n)\}$. `combinedProblem k E` is the decision problem over all levels $l\ge2$ (Appendix A.2.1): on input $\langle l-2,e\rangle$ it decides whether $\{n:B_e^{(l)}(n)\}$ is nonempty.
--
--   **Formalization Note.** Polynomials are `MvPolynomial (Fin m) ℤ`, evaluated at natural points via the coercion to $\mathbb Z$. In `Bgen`, index $0$ is the parameter $n$, indices $1,\dots,l-2$ are $z_2,\dots,z_{l-1}$, and the last $k$ indices are $x_1,\dots,x_k$; the `z`-quantifiers alternate starting with $\forall$, and the final $x$-block is all $\forall$ (even $l$, matrix $p_e\ne0$) or all $\exists$ (odd $l$, matrix $p_e=0$).
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), Appendix A (pp. 17–23); https://arxiv.org/abs/2610.08144. Standard background: R. I. Soare, Turing Computability, Springer 2016, Ch. 4. Specifically Example 4.1 (p. 13), Eq. (4.1), Eq. (A.3) (p. 19), Eq. (A.4) (p. 20), Appendix A.2.1 (pp. 22–23), and the Notation (Reducibility) pairing (p. 19).

import Mathlib

open Encodable
open scoped Classical

namespace AutoformalisationSCI

def cantorPair (x y : ℕ) : ℕ := (x + y) * (x + y + 1) + 2 * y

structure ComputablePolyEnum (m : ℕ) where
  p : ℕ → MvPolynomial (Fin m) ℤ
  surj : Function.Surjective p
  coeff_comp : Computable₂ (fun (e : ℕ) (s : Fin m → ℕ) =>
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm s) (p e))
  degBound : ℕ → ℕ
  degBound_comp : Computable degBound
  degBound_spec : ∀ e, (p e).totalDegree ≤ degBound e

def B (k : ℕ) (E : ComputablePolyEnum (k + 1)) (e n : ℕ) : Prop :=
  ∀ x : Fin k → ℕ,
    MvPolynomial.eval (fun i : Fin (k + 1) =>
      if h : i.val = 0 then (n : ℤ) else (x ⟨i.val - 1, by have := i.isLt; omega⟩ : ℤ)) (E.p e) ≠ 0

def dSet (k : ℕ) (E : ComputablePolyEnum (k + 1)) : Set ℕ := {e | ∃ n, B k E e n}

noncomputable def leastWitness (k : ℕ) (E : ComputablePolyEnum (k + 1)) (e : ℕ) : Option ℕ :=
  if h : ∃ n, B k E e n then some (Nat.find h) else none

def qtype (l k : ℕ) (i : Fin (l - 2 + k)) : Bool :=
  if (i : ℕ) < l - 2 then decide ((i : ℕ) % 2 = 0) else decide (l % 2 = 0)

def QuantVec : (r : ℕ) → (Fin r → Bool) → ((Fin r → ℕ) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | r + 1, q, P =>
      if q 0 = true then
        ∀ z : ℕ, QuantVec r (fun i => q i.succ) (fun zs => P (Fin.cons z zs))
      else
        ∃ z : ℕ, QuantVec r (fun i => q i.succ) (fun zs => P (Fin.cons z zs))

def Bgen (l k : ℕ) (hl : 2 ≤ l) (E : ComputablePolyEnum (l - 1 + k)) (e n : ℕ) : Prop :=
  QuantVec (l - 2 + k) (qtype l k) (fun v : Fin (l - 2 + k) → ℕ =>
    let pt : Fin (l - 1 + k) → ℕ :=
      fun i =>
        let j : Fin (l - 2 + k + 1) := Fin.cast (show l - 1 + k = l - 2 + k + 1 by omega) i
        if h : j.val = 0 then n else v ⟨j.val - 1, by have := j.isLt; omega⟩
    if l % 2 = 0 then MvPolynomial.eval (fun i => (pt i : ℤ)) (E.p e) ≠ 0
    else MvPolynomial.eval (fun i => (pt i : ℤ)) (E.p e) = 0)

def dSetL (l k : ℕ) (hl : 2 ≤ l) (E : ComputablePolyEnum (l - 1 + k)) : Set ℕ :=
  {e | ∃ n, Bgen l k hl E e n}

noncomputable def combinedProblem (k : ℕ) (E : ∀ l : ℕ, ComputablePolyEnum (l - 1 + k)) : ℕ → Bool :=
  fun p => if (∃ n, Bgen (p.unpair.1 + 2) k (by omega) (E (p.unpair.1 + 2)) p.unpair.2 n) then true else false

end AutoformalisationSCI


