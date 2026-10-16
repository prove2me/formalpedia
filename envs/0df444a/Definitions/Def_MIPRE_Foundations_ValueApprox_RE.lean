-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RE
-- name    : MIPRE_Foundations_ValueApprox_RE
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:19:15.174931+00:00
-- url     : https://prove2.me/theorems/92c4824b-8304-4857-8fb1-3a082196349e
-- title:
--   The quantum value of a described game is recursively enumerable from below
-- statement:
--   This bundle holds the module proving the $\mathrm{val}^*$ half of blueprint `lem:value-lower-approx`. It keeps no definitions; its two declarations are theorems. The first is a general closure principle: for `Primcodable` types $\alpha$, $\beta$ and a relation $p : \alpha \to \beta \to \mathrm{Prop}$ with `PrimrecRel p`, the predicate $a \mapsto \exists b,\, p\,a\,b$ is recursively enumerable (`REPred`). The second applies it to the certificate check of the previous module: for a game description $g$ (`GameData`) with associated game $G_g$ and a threshold given by naturals $p, q$,
--
--   $$\mathrm{REPred}\;\Big(\,(g, p, q) \mapsto \frac{p}{q} < \mathrm{val}^*(G_g)\,\Big) \quad \text{on } \mathrm{GameData} \times \mathbb{N} \times \mathbb{N},$$
--
--   where the division is in $\mathbb{R}$ and $\mathrm{val}^*$ is `quantumValue`. Together with the computable families of game descriptions of `MIPRE.Foundations.ClassMIPStarComputable`, this is what gives the inclusion $\mathrm{MIP}^* \subseteq \mathrm{RE}$ and the semideciders consumed by the compressibility criterion.
--
--   **Formalization Note** `REPred` is Mathlib's notion: the predicate is the domain of a partial computable function. The statement is on triples `x : GameData × ℕ × ℕ` and reads `(x.2.1 : ℝ) / x.2.2 < quantumValue x.1.game`; the cast and real division make the threshold `p / q` equal to `0` when `q = 0`, so that case tests `0 < val*`. Thresholds are nonnegative rationals given as fractions of naturals; the boundary case `val* = p / q` is not in the set, as the strict inequality says. The general lemma `REPred.of_primrecRel_exists` is stated for arbitrary `Primcodable α β` and a `PrimrecRel p`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RE.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RE.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec

/-!
# The quantum value is approximable from below: the `val*` half of `lem:value-lower-approx`

`MIPRE.ValueApprox.rePred_lt_quantumValue`: the set of pairs `(g, p / q)` of a game
description and a nonnegative rational threshold with `val*(G_g) > p / q` is recursively
enumerable, in Mathlib's sense (`REPred`, the domain of a partial computable function).

The procedure is the one of statement (S) in the paper's proof of `cor:mip-re`, with exact
candidates: dovetail over the raw candidates `r` (`RawStrategy`, a `Primcodable` type) and halt
on the first that passes the primitive recursive check `Check g p q r`. Some candidate passes
iff `p / q < val*(G_g)` (`exists_check_iff`), so the search halts exactly on the members of the
set; the boundary case `val* = p / q` is correctly non-halting.

Thresholds are nonnegative rationals given as fractions `p / q` of naturals, as in the paper's
(S) (`t ∈ [0, 1]`); a negative threshold is trivial, since `val* ≥ 0`. For `q = 0` the real
number `p / q` is `0`, and the check tests `0 < val*` accordingly.
-/

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)

/-- A predicate of the form `∃ b, p a b` with `p` primitive recursive is recursively enumerable:
search over the codes of `b`. -/
theorem REPred.of_primrecRel_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Prop} (hp : PrimrecRel p) : REPred fun a => ∃ b, p a b := by
  obtain ⟨inst, hp⟩ := hp
  -- the search predicate: decode `n` and test
  let q : α × ℕ → Bool := fun x =>
    ((Encodable.decode x.2 : Option β).map fun b => @decide (p x.1 b) (inst (x.1, b))).getD false
  have hq : Primrec q :=
    Primrec.option_getD.comp
      (Primrec.option_map (Primrec.decode.comp Primrec.snd)
        (hp.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)
      (Primrec.const false)
  have hpart : Partrec fun a : α => Nat.rfind fun n => (Part.some (q (a, n)) : Part Bool) :=
    Partrec.rfind (p := fun a n => (Part.some (q (a, n)) : Part Bool)) hq.to_comp.partrec
  refine hpart.dom_re.of_eq fun a => ?_
  refine (Nat.rfind_dom' (p := fun n => (Part.some (q (a, n)) : Part Bool))).trans ?_
  constructor
  · rintro ⟨n, hn, -⟩
    rw [Part.mem_some_iff] at hn
    revert hn
    simp only [q]
    cases h : (Encodable.decode n : Option β) with
    | none => simp
    | some b =>
      intro hb
      simp only [Option.map_some, Option.getD_some, Bool.true_eq, decide_eq_true_eq] at hb
      exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, ?_, fun _ => trivial⟩
    rw [Part.mem_some_iff]
    simp [q, Encodable.encodek, hb]

/-- **The quantum value from below** (the `val*` half of `lem:value-lower-approx`): the pairs
`(g, (p, q))` with `p / q < val*(G_g)` form a recursively enumerable set. -/
theorem rePred_lt_quantumValue :
    REPred fun x : GameData × ℕ × ℕ => (x.2.1 : ℝ) / x.2.2 < quantumValue x.1.game := by
  have h : PrimrecRel fun (x : GameData × ℕ × ℕ) (r : RawStrategy) => Check x.1 x.2.1 x.2.2 r :=
    primrecPred_check
  exact (REPred.of_primrecRel_exists h).of_eq fun x => exists_check_iff x.1 x.2.1 x.2.2

end MIPRE.ValueApprox


