-- Prove2me | Definitions.Def_MSKleene_SubstFam
-- name    : MSKleene_SubstFam
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:29:12.250536+00:00
-- url     : https://prove2.me/theorems/e2b11033-0bac-46c9-a8b3-892140750fbb
-- title:
--   Occurrence counting and family substitution
-- statement:
--   **Occurrence counting** and **family substitution** for a single variable (the operator $\left(\!\begin{smallmatrix}z\\(Q_\alpha)_{\alpha\in|P|_z}\end{smallmatrix}\!\right)(P)$ of Definition 3.13, used in Lemma 3.23, Corollary 3.17 and Lemma 3.18).
--
--   `Term.occ z P` is $|P|_z$, the number of occurrences of the variable `z` in `P`. `substFam z P qs` replaces, for every $\alpha \in \mathrm{Fin}\,|P|_z$, the $\alpha$-th occurrence of `z` in `P` (in left-to-right order) by the term `qs α`; it is implemented by threading the list `List.ofFn qs` through the term.
--
--   **Formalization Note** `noncomputable` because the variable-equality test uses classical decidability.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
Occurrence counting and family substitution for a single variable
(the operator `⟨z/(Q_α)_{α ∈ |P|_z}⟩(P)` of Definition 3.13, used in
Lemma 3.23, Corollary 3.17 and Lemma 3.18).

`Term.occ z P` is `|P|_z`, the number of occurrences of the variable `z` in `P`.
`substFam z P qs` replaces, for every `α`, the `α`-th occurrence of `z` in `P`
by the term `qs α`.
-/
import Definitions.Def_MSKleene_Term
import Mathlib.Data.List.OfFn

namespace MSKleene

open Classical

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

-- `Term.occ z P` = `|P|_z`, the number of occurrences of the variable `z`
-- (of sort `v`) in the term `P`.
mutual
noncomputable def Term.occ {v : S} (z : X v) : {s : S} → Term sig X s → ℕ
  | s, .var x => if h : s = v then (if (h ▸ x) = z then 1 else 0) else 0
  | _, .app _ ts => TermVec.occ z ts
noncomputable def TermVec.occ {v : S} (z : X v) : {w : List S} → TermVec sig X w → ℕ
  | _, .nil => 0
  | _, .cons t ts => Term.occ z t + TermVec.occ z ts
end

-- Auxiliary for `substFam`: substitute the terms of the list `qs` for the
-- successive occurrences of `z`, from left to right, returning the substituted
-- term and the unconsumed tail of `qs`.
mutual
noncomputable def Term.substFamAux {v : S} (z : X v) :
    {s : S} → Term sig X s → List (Term sig X v) →
      Term sig X s × List (Term sig X v)
  | s, .var x, qs =>
      if h : s = v then
        (if (h ▸ x) = z then
          (match qs with
            | [] => (Term.var x, [])
            | q :: qs' => (h.symm ▸ q, qs'))
         else (Term.var x, qs))
      else (Term.var x, qs)
  | _, .app σ ts, qs =>
      let r := TermVec.substFamAux z ts qs
      (Term.app σ r.1, r.2)
noncomputable def TermVec.substFamAux {v : S} (z : X v) :
    {w : List S} → TermVec sig X w → List (Term sig X v) →
      TermVec sig X w × List (Term sig X v)
  | _, .nil, qs => (.nil, qs)
  | _, .cons t ts, qs =>
      let r1 := Term.substFamAux z t qs
      let r2 := TermVec.substFamAux z ts r1.2
      (.cons r1.1 r2.1, r2.2)
end

/-- `substFam z P qs` — the substitution of the family `qs` for `z` in `P`
(Definition 3.13): the `α`-th occurrence of `z` in `P` is replaced by `qs α`. -/
noncomputable def substFam {v s : S} (z : X v) (P : Term sig X s)
    (qs : Fin (Term.occ z P) → Term sig X v) : Term sig X s :=
  (Term.substFamAux z P (List.ofFn qs)).1

end MSKleene


