-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
-- name    : MIPRE_Foundations_ValueApprox_RawPrimrec
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:17:16.484718+00:00
-- url     : https://prove2.me/theorems/6ee8e0a6-a0c2-498a-9d0b-4b95335fe932
-- title:
--   Primitive recursiveness of the certificate check for the quantum value
-- statement:
--   This bundle holds the module in which the certificate check of the quantum-value approximation is shown to be a primitive recursive predicate. Its inputs are a game description $g$ (`GameData`), a threshold given by naturals $p, q$, and a raw candidate strategy $r$ (`RawStrategy`: a denominator $k$, dimensions $d_A, d_B$, Gaussian-integer measurement matrices and a state vector $v$); $\mathrm{Check}\,g\,p\,q\,r$ says that $r$ certifies $p/q < \mathrm{val}^*(G_g)$.
--
--   The six definitions kept are type abbreviations for the uncurried contexts on which the lemmas are stated: $\mathrm{CheckCtx} = (\mathrm{GameData} \times \mathbb{N} \times \mathbb{N}) \times \mathrm{RawStrategy}$, the context $((g,p,q),r)$ of the check; $\mathrm{QuadCtx} = (\mathrm{GMat} \times \mathrm{GMat}) \times (\mathbb{N} \times \mathbb{N}) \times \mathrm{List}\,\mathrm{GInt}$, the context of the Born numerator; and $\mathrm{NumCtx}_1, \dots, \mathrm{NumCtx}_4$, the contexts of the numerator from the innermost level out, $\mathrm{NumCtx}_j$ being $(\mathrm{GameData} \times \mathrm{RawStrategy})$ paired on the left with $j$ natural indices. The main embedded result is
--
--   $$\mathrm{PrimrecPred}\;\big(((g,p,q),r) \mapsto \mathrm{Check}\,g\,p\,q\,r\big) \quad \text{on } \mathrm{CheckCtx}.$$
--
--   The other embedded lemmas are the primitive-recursiveness facts it is assembled from: the projections of `GameData`, list sums and bounded quantifiers, the integer sums `gsum`, `psum`, matrix entries and vector reads, the measurement checks (`IsHermRaw`, `IsIdemRaw`, `IsSumRaw`, `IsPVMRaw`), the Born numerator `quadRaw` and norm `normRaw`, the weights (`questionWeight`, `totalWeight`, `wt`, `W`, `Draw`), the numerator level by level, `matA`, `matB`, and the conjuncts of the check. The next module derives from it the recursive enumerability of the threshold set.
--
--   **Formalization Note** `Check g p q r` unfolds to `0 < r.k`, `IsPVMRaw (r.QA.getD x []) g.nA r.dA r.k` for all `x < g.nX + 1`, the same for `QB` and `y`, some `i < r.dA`, `j < r.dB` with `vget r.v (i * r.dB + j)` not `GInt.Eq'` to zero, and `ValueTest g p q r`, the inequality $p \cdot W \cdot k^2 \cdot \langle v, v\rangle < q \cdot \mathrm{numer}$ cleared of denominators ($0 < \mathrm{numer}$ when $q = 0$). The contexts are `abbrev`s; the lemmas are `Primrec`, `Primrec₂`, `PrimrecRel` or `PrimrecPred` statements on them, with `Primcodable` instances from the tuple equivalences of `GameData` and `RawStrategy`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RawPrimrec.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RawPrimrec.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
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

/-!
# The certificate check is primitive recursive

`MIPRE.ValueApprox.primrecPred_check`: `Check g p q r` is a primitive recursive predicate of
`(g, p, q, r)`. The proof follows the definitions in `MIPRE.Foundations.ValueApprox.RawStrategy`
one by one, with Mathlib's combinators for lists (`Primrec.list_map`, `list_getD`, `list_range`,
the bounded quantifiers `PrimrecRel.forall_lt`, `exists_lt`, `exists_mem_list`) and the arithmetic
of `MIPRE.Foundations.ValueApprox.RawInt`.
-/

namespace HaltingGameValue.GameData

theorem primrec_equivTuple : Primrec equivTuple := Primrec.of_equiv
theorem primrec_nX : Primrec nX := Primrec.fst.comp primrec_equivTuple
theorem primrec_nA : Primrec nA := (Primrec.fst.comp Primrec.snd).comp primrec_equivTuple
theorem primrec_w : Primrec w :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp primrec_equivTuple
theorem primrec_acc : Primrec acc :=
  (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp primrec_equivTuple

end HaltingGameValue.GameData

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)
open Primrec

/-! ## Generic combinators -/

theorem primrec_natSum : Primrec (List.sum : List ℕ → ℕ) :=
  (list_foldr Primrec.id (const 0)
    (nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun l => by
      simp [List.sum_eq_foldr]

theorem primrecPred_forall_lt {α : Type*} [Primcodable α] {n : α → ℕ} {p : α → ℕ → Prop}
    (hn : Primrec n) (hp : PrimrecRel p) : PrimrecPred fun a => ∀ i < n a, p a i := by
  have h1 : PrimrecRel fun (i : ℕ) (a : α) => p a i := hp.swap
  have h2 := (PrimrecRel.forall_mem_list h1).comp (list_range.comp hn) Primrec.id
  exact h2.of_eq fun a => by simp [List.mem_range]

theorem primrecPred_exists_lt {α : Type*} [Primcodable α] {n : α → ℕ} {p : α → ℕ → Prop}
    (hn : Primrec n) (hp : PrimrecRel p) : PrimrecPred fun a => ∃ i < n a, p a i := by
  have h1 : PrimrecRel fun (i : ℕ) (a : α) => p a i := hp.swap
  have h2 := (PrimrecRel.exists_mem_list h1).comp (list_range.comp hn) Primrec.id
  exact h2.of_eq fun a => by simp [List.mem_range]

theorem primrec_gsum {α : Type*} [Primcodable α] {n : α → ℕ} {f : α → ℕ → GInt} (hn : Primrec n)
    (hf : Primrec₂ f) : Primrec fun a => gsum (n a) (f a) :=
  GInt.primrec_sum.comp (list_map (list_range.comp hn) hf)

theorem primrec_psum {α : Type*} [Primcodable α] {n : α → ℕ} {f : α → ℕ → PInt} (hn : Primrec n)
    (hf : Primrec₂ f) : Primrec fun a => psum (n a) (f a) :=
  PInt.primrec_sum.comp (list_map (list_range.comp hn) hf)

theorem primrec_entry : Primrec fun p : GMat × ℕ × ℕ => entry p.1 p.2.1 p.2.2 :=
  (list_getD GInt.zero).comp ((list_getD []).comp fst (fst.comp snd)) (snd.comp snd)

theorem primrec_vget : Primrec fun p : List GInt × ℕ => vget p.1 p.2 :=
  (list_getD GInt.zero).comp fst snd

/-! ## The measurement checks -/

theorem primrecPred_isHermRaw : PrimrecPred fun p : GMat × ℕ => IsHermRaw p.1 p.2 := by
  -- body, as a relation in `j` and `((M, d), i)`
  have hbody : PrimrecRel fun (x : (GMat × ℕ) × ℕ) (j : ℕ) =>
      GInt.Eq' (entry x.1.1 x.2 j) (GInt.conj (entry x.1.1 j x.2)) :=
    GInt.primrecRel_eq'.comp
      (primrec_entry.comp ((fst.comp fst).comp fst |>.pair ((snd.comp fst).pair snd)))
      (GInt.primrec_conj.comp
        (primrec_entry.comp ((fst.comp fst).comp fst |>.pair (snd.pair (snd.comp fst)))))
  have hinner : PrimrecRel fun (p : GMat × ℕ) (i : ℕ) =>
      ∀ j < p.2, GInt.Eq' (entry p.1 i j) (GInt.conj (entry p.1 j i)) :=
    primrecPred_forall_lt (snd.comp fst) hbody
  exact primrecPred_forall_lt snd hinner

theorem primrecPred_isIdemRaw : PrimrecPred fun p : GMat × ℕ × ℕ => IsIdemRaw p.1 p.2.1 p.2.2 := by
  -- the sum `∑_{l < d} M i l * M l j`, as a function of `(((M, d, k), i), j)`
  have hsum : Primrec fun x : ((GMat × ℕ × ℕ) × ℕ) × ℕ =>
      gsum x.1.1.2.1 fun l => GInt.mul (entry x.1.1.1 x.1.2 l) (entry x.1.1.1 l x.2) :=
    primrec_gsum ((fst.comp snd).comp (fst.comp fst))
      (GInt.primrec_mul.comp
        (primrec_entry.comp
          (((fst.comp fst).comp (fst.comp fst)).pair ((snd.comp (fst.comp fst)).pair snd)))
        (primrec_entry.comp
          (((fst.comp fst).comp (fst.comp fst)).pair (snd.pair (snd.comp fst))))).to₂
  have hbody : PrimrecRel fun (x : (GMat × ℕ × ℕ) × ℕ) (j : ℕ) =>
      GInt.Eq' (gsum x.1.2.1 fun l => GInt.mul (entry x.1.1 x.2 l) (entry x.1.1 l j))
        (GInt.mul (GInt.ofNat x.1.2.2) (entry x.1.1 x.2 j)) :=
    GInt.primrecRel_eq'.comp hsum
      (GInt.primrec_mul.comp (GInt.primrec_ofNat.comp ((snd.comp snd).comp (fst.comp fst)))
        (primrec_entry.comp (((fst.comp fst).comp fst).pair ((snd.comp fst).pair snd))))
  have hinner : PrimrecRel fun (p : GMat × ℕ × ℕ) (i : ℕ) =>
      ∀ j < p.2.1, GInt.Eq' (gsum p.2.1 fun l => GInt.mul (entry p.1 i l) (entry p.1 l j))
        (GInt.mul (GInt.ofNat p.2.2) (entry p.1 i j)) :=
    primrecPred_forall_lt ((fst.comp snd).comp fst) hbody
  exact primrecPred_forall_lt (fst.comp snd) hinner

theorem primrecPred_isSumRaw :
    PrimrecPred fun p : List GMat × ℕ × ℕ × ℕ => IsSumRaw p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  -- `∑_{a ≤ nA} entry (Ms a) i j` as a function of `(((Ms, nA, d, k), i), j)`
  have hsum : Primrec fun x : ((List GMat × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      gsum (x.1.1.2.1 + 1) fun a => entry (x.1.1.1.getD a []) x.1.2 x.2 :=
    primrec_gsum (succ.comp ((fst.comp snd).comp (fst.comp fst)))
      (primrec_entry.comp
        (((list_getD []).comp ((fst.comp (fst.comp fst)).comp fst) snd).pair
          ((snd.comp (fst.comp fst)).pair (snd.comp fst)))).to₂
  have hbody : PrimrecRel fun (x : (List GMat × ℕ × ℕ × ℕ) × ℕ) (j : ℕ) =>
      GInt.Eq' (gsum (x.1.2.1 + 1) fun a => entry (x.1.1.getD a []) x.2 j)
        (if x.2 = j then GInt.ofNat x.1.2.2.2 else GInt.zero) :=
    GInt.primrecRel_eq'.comp hsum
      (Primrec.ite (Primrec.eq.comp (snd.comp fst) snd)
        (GInt.primrec_ofNat.comp ((snd.comp (snd.comp snd)).comp (fst.comp fst)))
        (const GInt.zero))
  have hinner : PrimrecRel fun (p : List GMat × ℕ × ℕ × ℕ) (i : ℕ) =>
      ∀ j < p.2.2.1, GInt.Eq' (gsum (p.2.1 + 1) fun a => entry (p.1.getD a []) i j)
        (if i = j then GInt.ofNat p.2.2.2 else GInt.zero) :=
    primrecPred_forall_lt ((fst.comp (snd.comp snd)).comp fst) hbody
  exact primrecPred_forall_lt (fst.comp (snd.comp snd)) hinner

theorem primrecPred_isPVMRaw :
    PrimrecPred fun p : List GMat × ℕ × ℕ × ℕ => IsPVMRaw p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hbody : PrimrecRel fun (p : List GMat × ℕ × ℕ × ℕ) (a : ℕ) =>
      IsHermRaw (p.1.getD a []) p.2.2.1 ∧ IsIdemRaw (p.1.getD a []) p.2.2.1 p.2.2.2 :=
    PrimrecPred.and
      (primrecPred_isHermRaw.comp
        (((list_getD []).comp (fst.comp fst) snd).pair ((fst.comp (snd.comp snd)).comp fst)))
      (primrecPred_isIdemRaw.comp
        (((list_getD []).comp (fst.comp fst) snd).pair
          (((fst.comp (snd.comp snd)).comp fst).pair ((snd.comp (snd.comp snd)).comp fst))))
  exact PrimrecPred.and (primrecPred_forall_lt (succ.comp (fst.comp snd)) hbody)
    primrecPred_isSumRaw

/-! ## The value

The compositions below are split into one lemma per level of summation, and intermediate facts
are stated without type ascriptions where their type is determined: elaborating a deep
composition against a large expected type is what exhausts the heartbeat budget, not the
mathematics. -/

/-- The context of the Born numerator: the two matrices, the two dimensions, the state. -/
abbrev QuadCtx := (GMat × GMat) × (ℕ × ℕ) × List GInt

/-- The innermost term of `quadRaw`, at `((((q, i), j), k), l)`. -/
theorem primrec_quadRawBody : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ =>
    GInt.mul (GInt.mul (GInt.conj (vget x.1.1.1.1.2.2 (x.1.1.1.2 * x.1.1.1.1.2.1.2 + x.1.1.2)))
      (GInt.mul (entry x.1.1.1.1.1.1 x.1.1.1.2 x.1.2) (entry x.1.1.1.1.1.2 x.1.1.2 x.2)))
      (vget x.1.1.1.1.2.2 (x.1.2 * x.1.1.1.1.2.1.2 + x.2)) := by
  have hq4 : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.1.1 :=
    fst.comp (fst.comp (fst.comp fst))
  have hi4 : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.1.2 :=
    snd.comp (fst.comp (fst.comp fst))
  have hj4 : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ => x.1.1.2 := snd.comp (fst.comp fst)
  have hk4 : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ => x.1.2 := snd.comp fst
  have hl4 : Primrec fun x : (((QuadCtx × ℕ) × ℕ) × ℕ) × ℕ => x.2 := snd
  have hdB4 := (snd.comp (fst.comp snd)).comp hq4
  have hvv4 := (snd.comp snd).comp hq4
  have hA4 := primrec_entry.comp (((fst.comp fst).comp hq4).pair (hi4.pair hk4))
  have hB4 := primrec_entry.comp (((snd.comp fst).comp hq4).pair (hj4.pair hl4))
  have hidx1 := nat_add.comp (nat_mul.comp hi4 hdB4) hj4
  have hidx2 := nat_add.comp (nat_mul.comp hk4 hdB4) hl4
  have hv1 := primrec_vget.comp (hvv4.pair hidx1)
  have hv2 := primrec_vget.comp (hvv4.pair hidx2)
  have hAB := GInt.primrec_mul.comp hA4 hB4
  have hc1 := GInt.primrec_conj.comp hv1
  have hcAB := GInt.primrec_mul.comp hc1 hAB
  have hfin := GInt.primrec_mul.comp hcAB hv2
  exact hfin

theorem primrec_quadRaw :
    Primrec fun q : QuadCtx => quadRaw q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.2.2 := by
  have h3 : Primrec fun x : ((QuadCtx × ℕ) × ℕ) × ℕ =>
      gsum x.1.1.1.2.1.2 fun l =>
        GInt.mul (GInt.mul (GInt.conj (vget x.1.1.1.2.2 (x.1.1.2 * x.1.1.1.2.1.2 + x.1.2)))
          (GInt.mul (entry x.1.1.1.1.1 x.1.1.2 x.2) (entry x.1.1.1.1.2 x.1.2 l)))
          (vget x.1.1.1.2.2 (x.2 * x.1.1.1.2.1.2 + l)) :=
    primrec_gsum ((snd.comp (fst.comp snd)).comp (fst.comp (fst.comp fst)))
      primrec_quadRawBody.to₂
  have h2 : Primrec fun x : (QuadCtx × ℕ) × ℕ =>
      gsum x.1.1.2.1.1 fun k => gsum x.1.1.2.1.2 fun l =>
        GInt.mul (GInt.mul (GInt.conj (vget x.1.1.2.2 (x.1.2 * x.1.1.2.1.2 + x.2)))
          (GInt.mul (entry x.1.1.1.1 x.1.2 k) (entry x.1.1.1.2 x.2 l)))
          (vget x.1.1.2.2 (k * x.1.1.2.1.2 + l)) :=
    primrec_gsum ((fst.comp (fst.comp snd)).comp (fst.comp fst)) h3.to₂
  have h1 : Primrec fun x : QuadCtx × ℕ =>
      gsum x.1.2.1.2 fun j => gsum x.1.2.1.1 fun k => gsum x.1.2.1.2 fun l =>
        GInt.mul (GInt.mul (GInt.conj (vget x.1.2.2 (x.2 * x.1.2.1.2 + j)))
          (GInt.mul (entry x.1.1.1 x.2 k) (entry x.1.1.2 j l)))
          (vget x.1.2.2 (k * x.1.2.1.2 + l)) :=
    primrec_gsum ((snd.comp (fst.comp snd)).comp fst) h2.to₂
  have h0 : Primrec fun q : QuadCtx =>
      gsum q.2.1.1 fun i => gsum q.2.1.2 fun j => gsum q.2.1.1 fun k => gsum q.2.1.2 fun l =>
        GInt.mul (GInt.mul (GInt.conj (vget q.2.2 (i * q.2.1.2 + j)))
          (GInt.mul (entry q.1.1 i k) (entry q.1.2 j l)))
          (vget q.2.2 (k * q.2.1.2 + l)) :=
    primrec_gsum (fst.comp (fst.comp snd)) h1.to₂
  exact h0.of_eq fun q => rfl

theorem primrec_normRaw : Primrec fun p : List GInt × ℕ × ℕ => normRaw p.1 p.2.1 p.2.2 := by
  -- level 2: `x = ((v, dA, dB), i), j)`
  have hidx : Primrec fun x : ((List GInt × ℕ × ℕ) × ℕ) × ℕ => x.1.2 * x.1.1.2.2 + x.2 :=
    nat_add.comp (nat_mul.comp (snd.comp fst) ((snd.comp snd).comp (fst.comp fst))) snd
  have hv : Primrec fun x : ((List GInt × ℕ × ℕ) × ℕ) × ℕ =>
      vget x.1.1.1 (x.1.2 * x.1.1.2.2 + x.2) :=
    primrec_vget.comp ((fst.comp (fst.comp fst)).pair hidx)
  have hmul : Primrec fun x : ((List GInt × ℕ × ℕ) × ℕ) × ℕ =>
      GInt.mul (GInt.conj (vget x.1.1.1 (x.1.2 * x.1.1.2.2 + x.2)))
        (vget x.1.1.1 (x.1.2 * x.1.1.2.2 + x.2)) :=
    GInt.primrec_mul.comp (GInt.primrec_conj.comp hv) hv
  have hbody : Primrec fun x : ((List GInt × ℕ × ℕ) × ℕ) × ℕ =>
      (GInt.mul (GInt.conj (vget x.1.1.1 (x.1.2 * x.1.1.2.2 + x.2)))
        (vget x.1.1.1 (x.1.2 * x.1.1.2.2 + x.2))).1 :=
    fst.comp hmul
  have h1 : Primrec fun y : (List GInt × ℕ × ℕ) × ℕ => psum y.1.2.2 fun j =>
      (GInt.mul (GInt.conj (vget y.1.1 (y.2 * y.1.2.2 + j)))
        (vget y.1.1 (y.2 * y.1.2.2 + j))).1 :=
    primrec_psum ((snd.comp snd).comp fst) hbody.to₂
  have h2 : Primrec fun p : List GInt × ℕ × ℕ => psum p.2.1 fun i => psum p.2.2 fun j =>
      (GInt.mul (GInt.conj (vget p.1 (i * p.2.2 + j))) (vget p.1 (i * p.2.2 + j))).1 :=
    primrec_psum (fst.comp snd) h1.to₂
  exact h2.of_eq fun p => rfl

theorem primrec_questionWeight :
    Primrec fun p : GameData × ℕ × ℕ => p.1.questionWeight p.2.1 p.2.2 := by
  have hR : PrimrecRel fun (t : ℕ × ℕ × ℕ) (b : ℕ × ℕ) => t.1 = b.1 ∧ t.2.1 = b.2 :=
    PrimrecPred.and (Primrec.eq.comp (fst.comp fst) (fst.comp snd))
      (Primrec.eq.comp ((fst.comp snd).comp fst) (snd.comp snd))
  have hfilter : Primrec fun p : GameData × ℕ × ℕ =>
      p.1.w.filter fun t => decide (t.1 = p.2.1 ∧ t.2.1 = p.2.2) :=
    (PrimrecRel.listFilter hR).comp (GameData.primrec_w.comp fst) snd
  have hmap : Primrec fun p : GameData × ℕ × ℕ =>
      (p.1.w.filter fun t => decide (t.1 = p.2.1 ∧ t.2.1 = p.2.2)).map fun t => t.2.2 :=
    list_map hfilter ((snd.comp snd).comp snd)
  have hsum := primrec_natSum.comp hmap
  exact hsum.of_eq fun p => rfl

theorem sum_range_eq_list_sum (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem totalWeight_eq (g : GameData) :
    g.totalWeight = ((List.range (g.nX + 1)).map fun x =>
      ((List.range (g.nX + 1)).map fun y => g.questionWeight x y).sum).sum := by
  unfold GameData.totalWeight
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin (g.nX + 1), g.questionWeight x y.val),
    sum_range_eq_list_sum]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun y => g.questionWeight x y), sum_range_eq_list_sum]

theorem primrec_questionWeight' :
    Primrec fun z : (GameData × ℕ) × ℕ => z.1.1.questionWeight z.1.2 z.2 := by
  have hargs : Primrec fun z : (GameData × ℕ) × ℕ => (z.1.1, z.1.2, z.2) :=
    (fst.comp fst).pair ((snd.comp fst).pair snd)
  have hqw := primrec_questionWeight.comp hargs
  exact hqw.of_eq fun z => rfl

theorem primrec_totalWeightInner : Primrec fun z : GameData × ℕ =>
    ((List.range (z.1.nX + 1)).map fun y => z.1.questionWeight z.2 y).sum := by
  have hmap := list_map (list_range.comp (succ.comp (GameData.primrec_nX.comp fst)))
    primrec_questionWeight'.to₂
  have hsum := primrec_natSum.comp hmap
  exact hsum.of_eq fun z => rfl

theorem primrec_totalWeight : Primrec GameData.totalWeight := by
  have hmap := list_map (list_range.comp (succ.comp GameData.primrec_nX))
    primrec_totalWeightInner.to₂
  have hsum := primrec_natSum.comp hmap
  exact hsum.of_eq fun g => (totalWeight_eq g).symm

theorem primrec_wt : Primrec fun p : GameData × ℕ × ℕ => wt p.1 p.2.1 p.2.2 := by
  have hzero : PrimrecPred fun p : GameData × ℕ × ℕ => p.1.totalWeight = 0 :=
    Primrec.eq.comp (primrec_totalWeight.comp fst) (const 0)
  have hpt : Primrec fun p : GameData × ℕ × ℕ => if p.2.1 = 0 ∧ p.2.2 = 0 then 1 else 0 :=
    Primrec.ite (PrimrecPred.and (Primrec.eq.comp (fst.comp snd) (const 0))
      (Primrec.eq.comp (snd.comp snd) (const 0))) (const 1) (const 0)
  have h : Primrec fun p : GameData × ℕ × ℕ =>
      if p.1.totalWeight = 0 then (if p.2.1 = 0 ∧ p.2.2 = 0 then 1 else 0)
      else p.1.questionWeight p.2.1 p.2.2 :=
    Primrec.ite hzero hpt primrec_questionWeight
  exact h.of_eq fun p => rfl

theorem primrec_W : Primrec W := by
  have h : Primrec fun g : GameData => if g.totalWeight = 0 then 1 else g.totalWeight :=
    Primrec.ite (Primrec.eq.comp primrec_totalWeight (const 0)) (const 1) primrec_totalWeight
  exact h.of_eq fun g => rfl

theorem primrec_Draw :
    Primrec fun p : GameData × ℕ × ℕ × ℕ × ℕ => Draw p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  have htuple : Primrec fun p : GameData × ℕ × ℕ × ℕ × ℕ =>
      (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2) := snd
  have hmem : PrimrecPred fun p : GameData × ℕ × ℕ × ℕ × ℕ =>
      (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2) ∈ p.1.acc := by
    have := (PrimrecRel.exists_mem_list (R := fun (t u : ℕ × ℕ × ℕ × ℕ) => t = u)
      Primrec.eq).comp (GameData.primrec_acc.comp fst) htuple
    exact this.of_eq fun p => by simp
  have hcond : PrimrecPred fun p : GameData × ℕ × ℕ × ℕ × ℕ =>
      p.2.1 = p.2.2.1 ∧ p.2.2.2.1 ≠ p.2.2.2.2 :=
    PrimrecPred.and (Primrec.eq.comp (fst.comp snd) (fst.comp (snd.comp snd)))
      (PrimrecPred.not (Primrec.eq.comp (fst.comp (snd.comp (snd.comp snd)))
        (snd.comp (snd.comp (snd.comp snd)))))
  have h : Primrec fun p : GameData × ℕ × ℕ × ℕ × ℕ =>
      if p.2.1 = p.2.2.1 ∧ p.2.2.2.1 ≠ p.2.2.2.2 then false
      else decide ((p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2) ∈ p.1.acc) :=
    Primrec.ite hcond (const false) (primrecPred_iff_primrec_decide.mp hmem)
  exact h.of_eq fun p => rfl

theorem primrec_matA : Primrec fun p : RawStrategy × ℕ × ℕ => p.1.matA p.2.1 p.2.2 :=
  (list_getD []).comp ((list_getD []).comp (RawStrategy.primrec_QA.comp fst) (fst.comp snd))
    (snd.comp snd)

theorem primrec_matB : Primrec fun p : RawStrategy × ℕ × ℕ => p.1.matB p.2.1 p.2.2 :=
  (list_getD []).comp ((list_getD []).comp (RawStrategy.primrec_QB.comp fst) (fst.comp snd))
    (snd.comp snd)

/-- The contexts of the numerator, from the innermost level `((((g, r), x), y), a), b)` out. -/
abbrev NumCtx4 := ((((GameData × RawStrategy) × ℕ) × ℕ) × ℕ) × ℕ
abbrev NumCtx3 := (((GameData × RawStrategy) × ℕ) × ℕ) × ℕ
abbrev NumCtx2 := ((GameData × RawStrategy) × ℕ) × ℕ
abbrev NumCtx1 := (GameData × RawStrategy) × ℕ

/-- The innermost term of `numer`. -/
theorem primrec_numerBody : Primrec fun x : NumCtx4 =>
    if Draw x.1.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2 = true then
      (quadRaw (x.1.1.1.1.2.matA x.1.1.1.2 x.1.2) (x.1.1.1.1.2.matB x.1.1.2 x.2)
        x.1.1.1.1.2.dA x.1.1.1.1.2.dB x.1.1.1.1.2.v).1
    else PInt.zero := by
  have hg4 : Primrec fun x : NumCtx4 => x.1.1.1.1.1 := fst.comp (fst.comp (fst.comp (fst.comp fst)))
  have hr4 : Primrec fun x : NumCtx4 => x.1.1.1.1.2 := snd.comp (fst.comp (fst.comp (fst.comp fst)))
  have hx4 : Primrec fun x : NumCtx4 => x.1.1.1.2 := snd.comp (fst.comp (fst.comp fst))
  have hy4 : Primrec fun x : NumCtx4 => x.1.1.2 := snd.comp (fst.comp fst)
  have ha4 : Primrec fun x : NumCtx4 => x.1.2 := snd.comp fst
  have hb4 : Primrec fun x : NumCtx4 => x.2 := snd
  have hmA := primrec_matA.comp (hr4.pair (hx4.pair ha4))
  have hmB := primrec_matB.comp (hr4.pair (hy4.pair hb4))
  have hdA := RawStrategy.primrec_dA.comp hr4
  have hdB := RawStrategy.primrec_dB.comp hr4
  have hvv := RawStrategy.primrec_v.comp hr4
  have hctx := (hmA.pair hmB).pair ((hdA.pair hdB).pair hvv)
  have hquad := primrec_quadRaw.comp hctx
  have hq1 := fst.comp hquad
  have hD := primrec_Draw.comp (hg4.pair (hx4.pair (hy4.pair (ha4.pair hb4))))
  have hDp := Primrec.eq.comp hD (const true)
  exact Primrec.ite hDp hq1 (const PInt.zero)

theorem primrec_numer3 : Primrec fun x : NumCtx3 =>
    psum (x.1.1.1.1.nA + 1) fun b =>
      if Draw x.1.1.1.1 x.1.1.2 x.1.2 x.2 b = true then
        (quadRaw (x.1.1.1.2.matA x.1.1.2 x.2) (x.1.1.1.2.matB x.1.2 b)
          x.1.1.1.2.dA x.1.1.1.2.dB x.1.1.1.2.v).1
      else PInt.zero :=
  primrec_psum (succ.comp (GameData.primrec_nA.comp (fst.comp (fst.comp (fst.comp fst)))))
    primrec_numerBody.to₂

theorem primrec_numer2sum : Primrec fun x : NumCtx2 =>
    psum (x.1.1.1.nA + 1) fun a => psum (x.1.1.1.nA + 1) fun b =>
      if Draw x.1.1.1 x.1.2 x.2 a b = true then
        (quadRaw (x.1.1.2.matA x.1.2 a) (x.1.1.2.matB x.2 b)
          x.1.1.2.dA x.1.1.2.dB x.1.1.2.v).1
      else PInt.zero :=
  primrec_psum (succ.comp (GameData.primrec_nA.comp (fst.comp (fst.comp fst))))
    primrec_numer3.to₂

theorem primrec_numer2wt : Primrec fun x : NumCtx2 => PInt.ofNat (wt x.1.1.1 x.1.2 x.2) := by
  have hargs : Primrec fun x : NumCtx2 => (x.1.1.1, x.1.2, x.2) :=
    (fst.comp (fst.comp fst)).pair ((snd.comp fst).pair snd)
  have h := PInt.primrec_ofNat.comp (primrec_wt.comp hargs)
  exact h.of_eq fun x => rfl

theorem primrec_numer2 : Primrec fun x : NumCtx2 =>
    PInt.mul (PInt.ofNat (wt x.1.1.1 x.1.2 x.2)) (psum (x.1.1.1.nA + 1) fun a =>
      psum (x.1.1.1.nA + 1) fun b =>
        if Draw x.1.1.1 x.1.2 x.2 a b = true then
          (quadRaw (x.1.1.2.matA x.1.2 a) (x.1.1.2.matB x.2 b)
            x.1.1.2.dA x.1.1.2.dB x.1.1.2.v).1
        else PInt.zero) :=
  PInt.primrec_mul.comp primrec_numer2wt primrec_numer2sum

theorem primrec_numer1 : Primrec fun x : NumCtx1 =>
    psum (x.1.1.nX + 1) fun y =>
      PInt.mul (PInt.ofNat (wt x.1.1 x.2 y)) (psum (x.1.1.nA + 1) fun a =>
        psum (x.1.1.nA + 1) fun b =>
          if Draw x.1.1 x.2 y a b = true then
            (quadRaw (x.1.2.matA x.2 a) (x.1.2.matB y b) x.1.2.dA x.1.2.dB x.1.2.v).1
          else PInt.zero) :=
  primrec_psum (succ.comp (GameData.primrec_nX.comp (fst.comp fst))) primrec_numer2.to₂

theorem primrec_numer : Primrec fun p : GameData × RawStrategy => numer p.1 p.2 := by
  have h0 : Primrec fun p : GameData × RawStrategy =>
      psum (p.1.nX + 1) fun x => psum (p.1.nX + 1) fun y =>
        PInt.mul (PInt.ofNat (wt p.1 x y)) (psum (p.1.nA + 1) fun a =>
          psum (p.1.nA + 1) fun b =>
            if Draw p.1 x y a b = true then
              (quadRaw (p.2.matA x a) (p.2.matB y b) p.2.dA p.2.dB p.2.v).1
            else PInt.zero) :=
    primrec_psum (succ.comp (GameData.primrec_nX.comp fst)) primrec_numer1.to₂
  exact h0.of_eq fun p => rfl

/-- The context of the check: `((g, p, q), r)`. -/
abbrev CheckCtx := (GameData × ℕ × ℕ) × RawStrategy

theorem primrecPred_valueTest :
    PrimrecPred fun p : CheckCtx => ValueTest p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hg : Primrec fun p : CheckCtx => p.1.1 := fst.comp fst
  have hr : Primrec fun p : CheckCtx => p.2 := snd
  have hnum := primrec_numer.comp (hg.pair hr)
  have hq : Primrec fun p : CheckCtx => p.1.2.2 := (snd.comp snd).comp fst
  have hp : Primrec fun p : CheckCtx => p.1.2.1 := (fst.comp snd).comp fst
  have hk := RawStrategy.primrec_k.comp hr
  have hq0 := Primrec.eq.comp hq (const 0)
  have hL := PrimrecPred.and hq0 (PInt.primrecRel_lt'.comp (const PInt.zero) hnum)
  have hcoef := nat_mul.comp (nat_mul.comp hp (primrec_W.comp hg)) (nat_mul.comp hk hk)
  have hnorm := primrec_normRaw.comp ((RawStrategy.primrec_v.comp hr).pair
      ((RawStrategy.primrec_dA.comp hr).pair (RawStrategy.primrec_dB.comp hr)))
  have hlhs := PInt.primrec_mul.comp (PInt.primrec_ofNat.comp hcoef) hnorm
  have hrhs := PInt.primrec_mul.comp (PInt.primrec_ofNat.comp hq) hnum
  have hR := PrimrecPred.and (PrimrecPred.not hq0) (PInt.primrecRel_lt'.comp hlhs hrhs)
  have h := PrimrecPred.or hL hR
  exact h.of_eq fun p => Iff.rfl

theorem primrecPred_checkA : PrimrecPred fun p : CheckCtx =>
    ∀ x < p.1.1.nX + 1, IsPVMRaw (p.2.QA.getD x []) p.1.1.nA p.2.dA p.2.k := by
  have hg : Primrec fun p : CheckCtx => p.1.1 := fst.comp fst
  have hr : Primrec fun p : CheckCtx => p.2 := snd
  have hnX : Primrec fun p : CheckCtx => p.1.1.nX + 1 := succ.comp (GameData.primrec_nX.comp hg)
  have hargs : Primrec fun z : CheckCtx × ℕ =>
      (z.1.2.QA.getD z.2 [], z.1.1.1.nA, z.1.2.dA, z.1.2.k) :=
    ((list_getD []).comp (RawStrategy.primrec_QA.comp (hr.comp fst)) snd).pair
      ((GameData.primrec_nA.comp (hg.comp fst)).pair
        ((RawStrategy.primrec_dA.comp (hr.comp fst)).pair (RawStrategy.primrec_k.comp (hr.comp fst))))
  have hbody : PrimrecRel fun (z : CheckCtx) (x : ℕ) =>
      IsPVMRaw (z.2.QA.getD x []) z.1.1.nA z.2.dA z.2.k :=
    primrecPred_isPVMRaw.comp hargs
  exact primrecPred_forall_lt hnX hbody

theorem primrecPred_checkB : PrimrecPred fun p : CheckCtx =>
    ∀ y < p.1.1.nX + 1, IsPVMRaw (p.2.QB.getD y []) p.1.1.nA p.2.dB p.2.k := by
  have hg : Primrec fun p : CheckCtx => p.1.1 := fst.comp fst
  have hr : Primrec fun p : CheckCtx => p.2 := snd
  have hnX : Primrec fun p : CheckCtx => p.1.1.nX + 1 := succ.comp (GameData.primrec_nX.comp hg)
  have hargs : Primrec fun z : CheckCtx × ℕ =>
      (z.1.2.QB.getD z.2 [], z.1.1.1.nA, z.1.2.dB, z.1.2.k) :=
    ((list_getD []).comp (RawStrategy.primrec_QB.comp (hr.comp fst)) snd).pair
      ((GameData.primrec_nA.comp (hg.comp fst)).pair
        ((RawStrategy.primrec_dB.comp (hr.comp fst)).pair (RawStrategy.primrec_k.comp (hr.comp fst))))
  have hbody : PrimrecRel fun (z : CheckCtx) (y : ℕ) =>
      IsPVMRaw (z.2.QB.getD y []) z.1.1.nA z.2.dB z.2.k :=
    primrecPred_isPVMRaw.comp hargs
  exact primrecPred_forall_lt hnX hbody

theorem primrecPred_checkVinner : PrimrecRel fun (z : CheckCtx × ℕ) (j : ℕ) =>
    ¬ GInt.Eq' (vget z.1.2.v (z.2 * z.1.2.dB + j)) GInt.zero := by
  have hr : Primrec fun z : (CheckCtx × ℕ) × ℕ => z.1.1.2 := (snd.comp fst).comp fst
  have hi : Primrec fun z : (CheckCtx × ℕ) × ℕ => z.1.2 := snd.comp fst
  have hj : Primrec fun z : (CheckCtx × ℕ) × ℕ => z.2 := snd
  have hidx := nat_add.comp (nat_mul.comp hi (RawStrategy.primrec_dB.comp hr)) hj
  have hvz := primrec_vget.comp ((RawStrategy.primrec_v.comp hr).pair hidx)
  have h := PrimrecPred.not (GInt.primrecRel_eq'.comp hvz (const GInt.zero))
  exact h.of_eq fun z => Iff.rfl

theorem primrecPred_checkVmid : PrimrecRel fun (p : CheckCtx) (i : ℕ) =>
    ∃ j < p.2.dB, ¬ GInt.Eq' (vget p.2.v (i * p.2.dB + j)) GInt.zero :=
  primrecPred_exists_lt (RawStrategy.primrec_dB.comp (snd.comp fst)) primrecPred_checkVinner

theorem primrecPred_checkV : PrimrecPred fun p : CheckCtx =>
    ∃ i < p.2.dA, ∃ j < p.2.dB, ¬ GInt.Eq' (vget p.2.v (i * p.2.dB + j)) GInt.zero :=
  primrecPred_exists_lt (RawStrategy.primrec_dA.comp snd) primrecPred_checkVmid

/-- The certificate check is primitive recursive. -/
theorem primrecPred_check :
    PrimrecPred fun p : CheckCtx => Check p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  have hk : PrimrecPred fun p : CheckCtx => 0 < p.2.k :=
    nat_lt.comp (const 0) (RawStrategy.primrec_k.comp snd)
  have h := PrimrecPred.and hk (PrimrecPred.and primrecPred_checkA
    (PrimrecPred.and primrecPred_checkB (PrimrecPred.and primrecPred_checkV primrecPred_valueTest)))
  exact h.of_eq fun p => Iff.rfl

end MIPRE.ValueApprox


