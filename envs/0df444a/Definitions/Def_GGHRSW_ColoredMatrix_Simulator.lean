-- Prove2me | Definitions.Def_GGHRSW_ColoredMatrix_Simulator
-- name    : GGHRSW_ColoredMatrix_Simulator
-- status  : Definition
-- author  : @Victorized
-- created : 2026-11-03T03:24:12.602593+00:00
-- url     : https://prove2.me/theorems/a1208ff0-f0bc-4e2d-b0bd-077ec97018f2
-- title:
--   App. C.3 — formal query expressions and the ideal (simulated) representation oracle
-- statement:
--   This file formalizes the bookkeeping of the simulator in the proof of Theorem 6 (App. C.3). For every handle the simulator remembers the *formal expression* that the adversary used to create it, not the matrix.
--
--   1. **Formal expressions** $e$ are terms built from the initial handles $\mathsf{init}(k)$, the $k$-th record of $DB(p,BP,(J,\sigma))$ in its public order, by $\mathsf{add}(e,e')$, $\mathsf{ConstMul}(e,a)$ and $\mathsf{mult}(e,e')$.
--   2. The **shape** of an expression (its dimensions and its left and right colours) is computed from the public shapes of the initial records alone. It depends neither on $\sigma$ nor on the sample. Ill-formed expressions (an unknown handle, or mismatched dimensions or colours) have no shape.
--   3. The **value** $e(\omega)$ of an expression at a sample $\omega$ of $\mathcal{RND}_p(BP)$ is computed with the oracle's own arithmetic mod $p$.
--   4. Two expressions are **identically equal** for $(J,\sigma)$ if $e(\omega)=e'(\omega)$ for every sample $\omega$.
--   5. The **ideal oracle** with an equality relation $E$ stores expressions instead of matrices. For a query it forms the requested expression $e$ and answers $\bot$ if $e$ is ill-formed. Otherwise it returns the first stored handle $h$ with $E(e_h,e)$, or, if there is none, it stores $e$ under a fresh handle and returns that handle.
--
--   With $E$ the identical-equality relation of $(J,\sigma)$, the ideal oracle's replies depend only on the adversary's coins, not on the sample; these replies are the simulated view. The real oracle compares the actual matrices mod $p$. The ideal oracle compares formal expressions by identical equality, which a simulator can decide without seeing the sample.
--
--   **Formalization Note.** Handles are 0-based indices into the stored list, exactly as for the real oracle (`initDB`, `respond`, `runFrom`), and the ideal oracle answers queries in the same order and with the same conventions for $\bot$ and handle reuse. The paper's simulator keeps formal polynomials and answers equality queries on full evaluations by querying $F|_\sigma$; here the decision rule is identical equality itself, and the fact that this rule depends only on $F|_\sigma$ is a separate statement (`GGHRSW.ColoredMatrix.theorem_6_identity_invariance`).
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), App. C.3, proof of Theorem 6, pp. 38–43 (the simulator)

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

namespace GGHRSW.ColoredMatrix

/-! ## Formal query expressions and the ideal (simulated) oracle (App. C.3) -/

/-- The shape `(rows, cols, LC, RC)` of a database record. -/
abbrev Shape := ℕ × ℕ × Color × Color

/-- The shape of a record. -/
def Record.shape {p : ℕ} (r : Record p) : Shape := (r.rows, r.cols, r.lc, r.rc)

/-- Shape of the record of step `i` (0-based) of the primal or dummy program. -/
def stepShape (n : ℕ) (primal : Bool) (i : ℕ) : Shape :=
  if primal then (NDim n, NDim n, .prim (i + 1), .prim (i + 2))
  else (NDim n, NDim n, .dum (i + 1), .dum (i + 2))

/-- Shapes of `programRecs bp J σ ω primal`, in the same order (they do not depend on `σ`, `ω`). -/
def programShapes (bp : BP) (J : Finset (Fin bp.ℓ)) (primal : Bool) : List Shape :=
  ((List.finRange bp.n).filter fun i => bp.inp i ∈ J).map (fun i => stepShape bp.n primal i.val) ++
    ((List.finRange bp.n).filter fun i => bp.inp i ∉ J).flatMap
      (fun i => [stepShape bp.n primal i.val, stepShape bp.n primal i.val])

/-- Shapes of the initial database `DB(p, BP, (J, σ))`, in its public order. -/
def initShapes (bp : BP) (J : Finset (Fin bp.ℓ)) : List Shape :=
  [(1, NDim bp.n, .src, .prim 1), (1, NDim bp.n, .src, .dum 1),
   (NDim bp.n, 1, .prim (bp.n + 1), .snk), (NDim bp.n, 1, .dum (bp.n + 1), .snk)] ++
  programShapes bp J true ++ programShapes bp J false

/-- Formal expressions built by the adversary's queries from the handles of the initial database:
`init k` is the `k`-th initial record; `add`, `constMul`, `mult` mirror the three query types. -/
inductive QExpr (p : ℕ)
  | init (k : ℕ)
  | add (e e' : QExpr p)
  | constMul (e : QExpr p) (a : ZMod p)
  | mult (e e' : QExpr p)

namespace QExpr

variable {p : ℕ}

/-- The shape of an expression, computed from the public shapes alone (`none` = ill-formed:
unknown handle or a dimension/colour mismatch). -/
def shape (bp : BP) (J : Finset (Fin bp.ℓ)) : QExpr p → Option Shape
  | .init k => (initShapes bp J)[k]?
  | .add e e' => (e.shape bp J).bind fun s => (e'.shape bp J).bind fun s' =>
      if s = s' then some s else none
  | .constMul e _ => e.shape bp J
  | .mult e e' => (e.shape bp J).bind fun s => (e'.shape bp J).bind fun s' =>
      if s.2.1 = s'.1 ∧ s.2.2.2 = s'.2.2.1 then some (s.1, s'.2.1, s.2.2.1, s'.2.2.2) else none

/-- The value of an expression when the initial database is `db` (the oracle's arithmetic). -/
def eval (db : List (Record p)) : QExpr p → Option (Record p)
  | .init k => db[k]?
  | .add e e' => (e.eval db).bind fun r => (e'.eval db).bind fun r' => addRec r r'
  | .constMul e a => (e.eval db).map fun r => constMulRec r a
  | .mult e e' => (e.eval db).bind fun r => (e'.eval db).bind fun r' => multRec r r'

end QExpr

/-- Two expressions are identically equal for `(J, σ)`: their values agree for every sample of
`RND_p(BP)`. -/
def IdenticallyEqual {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (e e' : QExpr p) : Prop :=
  ∀ ω : Sample p bp, e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω)

/-- The formal expression requested by a query (`none` for an unknown handle). -/
def queryExpr {p : ℕ} (db : List (QExpr p)) : Query p → Option (QExpr p)
  | .add h h' => (db[h]?).bind fun e => (db[h']?).map fun e' => .add e e'
  | .constMul h a => (db[h]?).map fun e => .constMul e a
  | .mult h h' => (db[h]?).bind fun e => (db[h']?).map fun e' => .mult e e'

open Classical in
/-- One step of the ideal oracle, which stores formal expressions and decides equality with the
relation `E` (for the simulator: `IdenticallyEqual`) instead of comparing actual matrices. -/
noncomputable def idealStep {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ))
    (E : QExpr p → QExpr p → Prop) (db : List (QExpr p)) (Q : Query p) :
    List (QExpr p) × Option ℕ :=
  match queryExpr db Q with
  | none => (db, none)
  | some e =>
    if (e.shape bp J).isNone then (db, none) else
    match db.findIdx? (fun x => decide (E x e)) with
    | some h => (db, some h)
    | none => (db ++ [e], some db.length)

/-- Run `k` more interactions of `A` with the ideal oracle. -/
noncomputable def idealRunFrom {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ))
    (E : QExpr p → QExpr p → Prop) (A : Adversary p) (c : Fin A.K) :
    ℕ → List (QExpr p) × List (Option ℕ) → List (QExpr p) × List (Option ℕ)
  | 0, s => s
  | k + 1, s =>
    let r := idealStep bp J E s.1 (A.next c s.2)
    idealRunFrom bp J E A c k (r.1, s.2 ++ [r.2])

/-- The initial handles `init 0, …, init (|DB| - 1)`. -/
def initExprs {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ)) : List (QExpr p) :=
  (List.range (initShapes bp J).length).map QExpr.init

/-- The simulated view: the replies of `A` (with coins `c`) against the ideal oracle deciding
equality with `E`. With `E = IdenticallyEqual bp J σ` this is the simulator's output. -/
noncomputable def idealView {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ))
    (E : QExpr p → QExpr p → Prop) (A : Adversary p) (c : Fin A.K) : List (Option ℕ) :=
  (idealRunFrom bp J E A c A.q (initExprs bp J, [])).2

end GGHRSW.ColoredMatrix


