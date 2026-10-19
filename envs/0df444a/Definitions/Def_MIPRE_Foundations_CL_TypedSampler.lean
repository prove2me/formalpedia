-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_TypedSampler
-- name    : MIPRE_Foundations_CL_TypedSampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:59.978623+00:00
-- url     : https://prove2.me/theorems/a239b47a-1acb-480c-a9c6-3c5e904e8459
-- title:
--   Definitions of TypedSampler: Typed samplers with an ambient program The typed version of the sampler interface in `types.tex`
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.TypedSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Typed samplers with an ambient program. The typed version of the sampler interface in `types.tex`. There is a single program and a common ambient dimension. A dimension query carries no type; every other query carries the selected type together with the usual query.
--
--   **Definitions** (6): `MIPRE.CL.TypedSampler` (A typed sampler has one executable query interface for all types, rather than a nonuniform collection of independently chosen programs.); `MIPRE.CL.TypedSampler.Query`; `MIPRE.CL.TypedSampler.Query.instSizedEncoding`; `MIPRE.CL.TypedSampler.Query.ofData`; `MIPRE.CL.TypedSampler.Query.toData`; `MIPRE.CL.TypedSampler.TimeBoundAt`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ofData_toData`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.TypedSampler` (`MIPRE/Foundations/CL/TypedSampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 8 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/TypedSampler.lean; blueprint def:typed-sampler-interface

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/TypedSampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler

/-! # Typed samplers with an ambient program

The typed version of the sampler interface in `types.tex`. There is a single
program and a common ambient dimension. A dimension query carries no type;
every other query carries the selected type together with the usual query.
-/

namespace MIPRE.CL

open Cost

inductive TypedSampler.Query (T : Type*)
  | dimension
  | atType (type : T) (query : Sampler.Query)

namespace TypedSampler.Query

variable {T : Type*} [SizedEncoding T]

def toData : Query T → Data
  | .dimension => .nil
  | .atType t q => .cons (encode t) (encode q)

def ofData : Data → Option (Query T)
  | .nil => some .dimension
  | .cons t q => (decode t : Option T).bind fun t' =>
      (decode q : Option Sampler.Query).map (Query.atType t')

@[simp] theorem ofData_toData (q : Query T) : ofData (toData q) = some q := by
  cases q <;> simp [toData, ofData, SizedEncoding.decode_encode]

instance : SizedEncoding (Query T) where
  encode := toData
  decode := ofData
  decode_encode := ofData_toData

end TypedSampler.Query

/-- A typed sampler has one executable query interface for all types, rather
than a nonuniform collection of independently chosen programs. -/
structure TypedSampler (ℓ : ℕ) (T : Type*) [SizedEncoding T] where
  prog : Prog
  closed : prog.WellScoped 1
  dim : ℕ → ℕ
  cl : (n : ℕ) → Player → T → CLFun 𝔽₂ (Fin (dim n)) ℓ
  cl_exactlyOn : ∀ n w t, (cl n w t).ExactlyOn Finset.univ
  runs_dimension : ∀ n, ∃ time,
    prog.Runs (encode (n, (TypedSampler.Query.dimension : TypedSampler.Query T)))
      (encode (dim n)) time
  runs_marginal : ∀ n w t j (z : BitStr), 1 ≤ j → j ≤ ℓ → z.length = dim n →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.marginal w j z)))
      (encode (toBits (((cl n w t).truncate j).eval (ofBits (dim n) z)))) time
  runs_linear : ∀ n w t j (u y : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w t).truncate (j - 1)).eval x)) → y.length = dim n →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.linear w j u y)))
      (encode (toBits ((cl n w t).mapOfPrefix (j - 1)
        (ofBits (dim n) u) (ofBits (dim n) y)))) time
  runs_factor : ∀ n w t j (u : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w t).truncate (j - 1)).eval x)) →
    ∃ time, prog.Runs (encode (n, TypedSampler.Query.atType t (.factor w j u)))
      (encode (indicatorBits ((cl n w t).factorOfPrefix (j - 1) (ofBits (dim n) u)))) time
  halts : ∀ (n : ℕ) (d : Data), Halts prog (.cons (encode n) d)

namespace TypedSampler

variable {ℓ : ℕ} {T : Type*} [SizedEncoding T]

def TimeBoundAt (S : TypedSampler ℓ T) (n B k : ℕ) : Prop :=
  ∀ d, HaltsWithin S.prog (.cons (encode n) d) (B * (d.size + 1) ^ k)

end TypedSampler
end MIPRE.CL


