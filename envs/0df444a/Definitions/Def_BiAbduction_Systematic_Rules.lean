-- Prove2me | Definitions.Def_BiAbduction_Systematic_Rules
-- name    : BiAbduction_Systematic_Rules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:06.311989+00:00
-- url     : https://prove2.me/theorems/ecb825a4-166e-475e-aefd-414db31859ec
-- title:
--   Figure 2 — proof rules for perfect abductive inference modulo ≤c
-- statement:
--   This file defines the judgment $\Delta*[D]\triangleright H$ of Figure 2 as an inductive relation. Write $\Sigma\equiv L_1\mapsto R_1*\dots*L_n\mapsto R_n$ for the spatial part of the left-hand side and $\Sigma^{-j}$ for $\Sigma$ with its $j$-th conjunct removed. The rules are:
--
--   1. **false**: $(\Pi\wedge\Sigma)*[\mathsf{false}]\triangleright \Pi'\wedge\mathsf{emp}$, provided $\Sigma$ contains at least one points-to fact;
--   2. **emp**: $(\Pi\wedge\mathsf{emp})*[\Pi'\wedge\mathsf{emp}]\triangleright\Pi'\wedge\mathsf{emp}$;
--   3. **true**: $(\Pi\wedge\Sigma)*[\Pi'\wedge\mathsf{emp}]\triangleright\Pi'\wedge\mathsf{true}$;
--   4. **psto**: if $(\Pi\wedge\Sigma^{-j})*[D_j]\triangleright\Pi'\wedge\Sigma'$ for every $j=1,\dots,n$ and $(\Pi\wedge\Sigma)*[D]\triangleright\Pi'\wedge\Sigma'$, then
--   $$(\Pi\wedge\Sigma)*\Big[\textstyle\bigvee_{j=1}^n(L_j=L'\wedge R_j=R'\wedge D_j)\ \vee\ (D*L'\mapsto R')\Big]\triangleright \Pi'\wedge L'\mapsto R'*\Sigma',$$
--   where $L'\mapsto R'$ may be any points-to conjunct of the right-hand side;
--   5. **exists**: if $\Delta*[D]\triangleright\Delta'$ with $\Delta'$ quantifier-free, then $\Delta*[\exists\vec X.D]\triangleright\exists\vec X.\Delta'$.
--
--   Conjoining atoms to a disjunction, $*$-conjoining $L'\mapsto R'$ to it and prefixing $\exists\vec X$ act disjunct by disjunct (p. 26). The relation is the proof system whose derivable solutions are minimal w.r.t. $\le_c$ (§3.4.2).
--
--   **Formalization Note** The judgment is a relation, not a function: psto may select any points-to conjunct $L'\mapsto R'$ of the right-hand side (index `k`), and its premises include one derivation for every $j$. A quantifier-free right-hand side $\Pi'\wedge\Sigma'$ is the symbolic heap with no bound variables; the premise of exists must have such a right-hand side.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 28, Figure 2; p. 26 (∃X. D shorthand)

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

namespace BiAbduction.Systematic

/-!
Figure 2 (p. 28): proof rules for perfect abductive inference modulo `≤c`, judgments
`Δ ∗ [D] ▷ H`.
-/

/-- Conjoin pure atoms to (the body of) a disjunct. -/
def addAtoms (as : List PureAtom) (H : SH) : SH := (H.1, (as ++ H.2.1, H.2.2.1, H.2.2.2))

/-- `∗`-conjoin a points-to fact to (the body of) a disjunct. -/
def addPts (pt : PtsTo) (H : SH) : SH := (H.1, (H.2.1, pt :: H.2.2.1, H.2.2.2))

/-- Prefix existential quantifiers `∃X⃗` to a disjunct. -/
def bindVars (X : List ℕ) (H : SH) : SH := (X ++ H.1, H.2)

/-- `Derives Δ D H` is the judgment `Δ ∗ [D] ▷ H` of Figure 2. A quantifier-free right-hand side
`Π' ∧ Σ'` is the symbolic heap `([], (Π', Σ', tr))`. -/
inductive Derives : LHS → Disj → SH → Prop
  /-- `(Π ∧ E↦E' ∗ Σ) ∗ [false] ▷ Π' ∧ emp`: the left-hand side has at least one points-to fact. -/
  | false_ax (pi : List PureAtom) (sig : List PtsTo) (pi' : List PureAtom) (hsig : sig ≠ []) :
      Derives (pi, sig) [] ([], (pi', [], false))
  /-- `(Π ∧ emp) ∗ [Π' ∧ emp] ▷ Π' ∧ emp`. -/
  | emp_ax (pi pi' : List PureAtom) :
      Derives (pi, []) [([], (pi', [], false))] ([], (pi', [], false))
  /-- `(Π ∧ Σ) ∗ [Π' ∧ emp] ▷ Π' ∧ true`. -/
  | true_ax (pi : List PureAtom) (sig : List PtsTo) (pi' : List PureAtom) :
      Derives (pi, sig) [([], (pi', [], false))] ([], (pi', [], true))
  /-- psto: with `Σ ≡ ∗ᵢ Lᵢ↦Rᵢ` and `L'↦R'` the `k`-th points-to fact of the right-hand side,
  from `(Π ∧ Σ⁻ʲ) ∗ [Dⱼ] ▷ Π' ∧ Σ'` for every `j` and `(Π ∧ Σ) ∗ [D] ▷ Π' ∧ Σ'` derive
  `(Π ∧ Σ) ∗ [⋁ⱼ (Lⱼ=L' ∧ Rⱼ=R' ∧ Dⱼ) ∨ (D ∗ L'↦R')] ▷ Π' ∧ L'↦R' ∗ Σ'`. -/
  | psto (pi : List PureAtom) (sig : List PtsTo) (pi' : List PureAtom) (sig' : List PtsTo)
      (tr : Bool) (k : Fin sig'.length) (Ds : Fin sig.length → Disj) (D : Disj)
      (hj : ∀ j : Fin sig.length,
        Derives (pi, sig.eraseIdx j) (Ds j) ([], (pi', sig'.eraseIdx k, tr)))
      (h : Derives (pi, sig) D ([], (pi', sig'.eraseIdx k, tr))) :
      Derives (pi, sig)
        ((List.finRange sig.length).flatMap (fun j =>
            (Ds j).map (addAtoms [(true, (sig.get j).1, (sig'.get k).1),
                                  (true, (sig.get j).2, (sig'.get k).2)])) ++
          D.map (addPts (sig'.get k)))
        ([], (pi', sig', tr))
  /-- exists: from `Δ ∗ [D] ▷ Δ'` derive `Δ ∗ [∃X⃗. D] ▷ ∃X⃗. Δ'`. -/
  | exists_r (Δ : LHS) (D : Disj) (q : QF) (X : List ℕ) (h : Derives Δ D ([], q)) :
      Derives Δ (D.map (bindVars X)) (X, q)

end BiAbduction.Systematic


