-- Prove2me | Definitions.Def_erdos501_zfset_structure
-- name    : erdos501_zfset_structure
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:15:53.959232+00:00
-- url     : https://prove2.me/theorems/8559db0a-2c4b-4ec7-9987-535a16afacec
-- title:
--   The standard set-theory structure on Mathlib's ZFSet
-- statement:
--   The standard interpretation of the set-theory language $L$ on Mathlib's `ZFSet`: $\emptyset \mapsto \emptyset$, $\omega \mapsto$ `ZFSet.omega`, $\mathcal{P} \mapsto$ `ZFSet.powerset`, $\bigcup \mapsto$ `ZFSet.sUnion`, $(\cdot,\cdot) \mapsto$ the Kuratowski pair `ZFSet.pair`, and $\in \mapsto \in$.
--
--   This is the structure in which the faithfulness target (Target 7) evaluates the sentence $\varphi_{501}$: it certifies that the first-order rendering of Erdős Problem 501 means, in the standard set-theoretic universe, exactly the Mathlib-level statement of the first question.
--
--   **Formalization Note.** A `noncomputable instance` of `L.Structure ZFSet.{0}`; function and relation symbols are interpreted by pattern matching on the symbol. Ported verbatim from Part A of `Challenge.lean`.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L530-L544 (Part A, zfsetStructure)

/- Ported verbatim from elliotglazer/erdos501, Challenge.lean (Apache 2.0, (c) 2026 Elliot Glazer),
   commit 218d1c1e46f77d4db80e566d1721782e85b94a17. -/
import Mathlib.SetTheory.ZFC.Basic
import Definitions.Def_definable_saturated_fol

open FirstOrder FirstOrder.Language

namespace Erdos501.FOL

/-! ### The standard interpretation in Mathlib's `ZFSet` -/

/-- Mathlib's `ZFSet` as an `L`-structure: `∅ ↦ ∅`, `ω ↦ ω`, `𝒫 ↦ powerset`,
`⋃ ↦ sUnion`, `(·,·) ↦ Kuratowski pair`, `∈ ↦ ∈`. -/
noncomputable instance zfsetStructure : L.Structure ZFSet.{0} where
  funMap {n} f xs :=
    match n, f, xs with
    | _, Func.emptyset, _ => ∅
    | _, Func.omega, _ => ZFSet.omega
    | _, Func.powerset, xs => ZFSet.powerset (xs 0)
    | _, Func.union, xs => ZFSet.sUnion (xs 0)
    | _, Func.pair, xs => ZFSet.pair (xs 0) (xs 1)
  RelMap {n} r xs :=
    match n, r, xs with
    | _, Rel.mem, xs => xs 0 ∈ xs 1

end Erdos501.FOL


