-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularComplete
-- name    : MIPRE_Foundations_OracularComplete
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:18.822034+00:00
-- url     : https://prove2.me/theorems/69956e89-2b9f-4d47-95ee-9c233dce7f10
-- title:
--   Definitions of OracularComplete: Completeness of oracularization Item 1 of blueprint `thm:oracularization`: a value-`1` PCC strategy for the input game…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularComplete` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Completeness of oracularization. Item 1 of blueprint `thm:oracularization`: a value-`1` PCC strategy for the input game gives one for the oracularized game of `MIPRE.SeededGame.oracular`. The honest oracle measures the input strategy's *two* measurements jointly: at seed `z` its operator for the answer pair `(a, b)` is `M^{(false, L^𝖠 z)}_a · M^{(true, L^𝖡 z)}_b`. That product is a projection exactly because the two commute, which is what `IsPCC` supplies at the question pair the seed determines — and the seed always determines a pair of positive weight, since `z` itself lies in its fibre…
--
--   **Definitions** (3): `MIPRE.SeededGame.oracleMeas` (The honest oracularized measurement family.); `MIPRE.SeededGame.oracleOp` (The operators of the honest oracularized strategy: an oracle measures the input strategy's two measurements jointly, an isolated player the…); `MIPRE.SeededGame.oracleStrategy` (The honest strategy for the oracularized game: the same Hilbert space as the input strategy, the joint measurement for an oracle, and the…).
--
--   **Embedded lemmas** (11): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `commute_of_isPCC`, `dist_pos`, `doubled_mu_pos`, `oracleMeas_M`, `oracleOp_alice_pair`, `oracleOp_alice_single`, `oracleOp_bob_pair`, `oracleOp_bob_single`, `oracleOp_oracle_pair`, `oracleOp_oracle_single`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularComplete` (`MIPRE/Foundations/OracularComplete.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularComplete.lean; blueprint lem:oracular-completeness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularComplete.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Theorems.Thm_MIPRE_OAns_sum_eq

/-!
# Completeness of oracularization

Item 1 of blueprint `thm:oracularization`: a value-`1` PCC strategy for the input game gives
one for the oracularized game of `MIPRE.SeededGame.oracular`.

The honest oracle measures the input strategy's *two* measurements jointly: at seed `z` its
operator for the answer pair `(a, b)` is `M^{(false, L^𝖠 z)}_a · M^{(true, L^𝖡 z)}_b`. That
product is a projection exactly because the two commute, which is what `IsPCC` supplies at the
question pair the seed determines — and the seed always determines a pair of positive weight,
since `z` itself lies in its fibre (`dist_pos`).

Repair 2 of `rem:oracularization-repairs` --- that the completeness witness has *identical
measurement operators* for the two players rather than a symmetric state, the campaign having
found the symmetry claim unjustified --- is structural here: a `SyncStrategy` is one family of
projective measurements played by both players, so there is nothing to arrange.
-/

namespace MIPRE

open Finset Matrix

namespace SeededGame

variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)

/-! ## The seed always lands on a question pair of positive weight -/

omit [Fintype A] [DecidableEq A] in

theorem dist_pos (z : V) : 0 < S.dist (S.LA z) (S.LB z) := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine div_pos ?_ hcard
  have hz : z ∈ univ.filter fun w => S.LA w = S.LA z ∧ S.LB w = S.LB z :=
    mem_filter.mpr ⟨mem_univ z, rfl, rfl⟩
  exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩

theorem doubled_mu_pos (z : V) :
    0 < S.toGame.doubled.μ (false, S.LA z) (true, S.LB z) := by
  rw [Game.doubled_μ]
  simpa using S.dist_pos z

/-! ## The oracle's joint measurement -/

variable {S}

/-- The commutation the oracle's joint measurement needs, from `IsPCC` at the question pair the
seed determines. -/
theorem commute_of_isPCC {T : SyncStrategy S.toGame.doubled} (hT : T.IsPCC)
    (z : V) (a b : A) :
    T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b
      = T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a :=
  hT _ _ (S.doubled_mu_pos z) a b

variable (S)

/-- The operators of the honest oracularized strategy: an oracle measures the input strategy's
two measurements jointly, an isolated player the one the input strategy would have used, and a
shape that does not match the role gets `0`. -/
noncomputable def oracleOp (T : SyncStrategy S.toGame.doubled) :
    Role × V → OAns A → Matrix (Fin T.d) (Fin T.d) ℂ
  | (.oracle, z), .pair a b => T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b
  | (.alice, x), .single a => T.P.M (false, x) a
  | (.bob, y), .single b => T.P.M (true, y) b
  | _, _ => 0

variable {S}

@[simp] theorem oracleOp_oracle_pair (T : SyncStrategy S.toGame.doubled) (z : V) (a b : A) :
    S.oracleOp T (.oracle, z) (.pair a b)
      = T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b := rfl

@[simp] theorem oracleOp_oracle_single (T : SyncStrategy S.toGame.doubled) (z : V) (a : A) :
    S.oracleOp T (.oracle, z) (.single a) = 0 := rfl

@[simp] theorem oracleOp_alice_single (T : SyncStrategy S.toGame.doubled) (x : V) (a : A) :
    S.oracleOp T (.alice, x) (.single a) = T.P.M (false, x) a := rfl

@[simp] theorem oracleOp_alice_pair (T : SyncStrategy S.toGame.doubled) (x : V) (a b : A) :
    S.oracleOp T (.alice, x) (.pair a b) = 0 := rfl

@[simp] theorem oracleOp_bob_single (T : SyncStrategy S.toGame.doubled) (y : V) (b : A) :
    S.oracleOp T (.bob, y) (.single b) = T.P.M (true, y) b := rfl

@[simp] theorem oracleOp_bob_pair (T : SyncStrategy S.toGame.doubled) (y : V) (a b : A) :
    S.oracleOp T (.bob, y) (.pair a b) = 0 := rfl

/-- The honest oracularized measurement family. Projectivity of the oracle's operators is
where the commutation of `IsPCC` is used. -/
noncomputable def oracleMeas (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    ProjectiveMeasurement (Role × V) (OAns A) (Matrix (Fin T.d) (Fin T.d) ℂ) where
  M := S.oracleOp T
  selfAdjoint := by
    rintro ⟨r, z⟩ u
    cases r <;> cases u
    · simp only [oracleOp_oracle_pair, star_mul, T.P.selfAdjoint]
      exact (commute_of_isPCC hT z _ _).symm
    · simp
    · simp
    · simp [T.P.selfAdjoint]
    · simp
    · simp [T.P.selfAdjoint]
  projective := by
    rintro ⟨r, z⟩ u
    cases r <;> cases u
    · rename_i a b
      have hP := T.P.projective (false, S.LA z) a
      have hQ := T.P.projective (true, S.LB z) b
      calc T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b *
              (T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b)
          = T.P.M (false, S.LA z) a * (T.P.M (true, S.LB z) b *
              T.P.M (false, S.LA z) a) * T.P.M (true, S.LB z) b := by noncomm_ring
        _ = T.P.M (false, S.LA z) a * (T.P.M (false, S.LA z) a *
              T.P.M (true, S.LB z) b) * T.P.M (true, S.LB z) b := by
            rw [← commute_of_isPCC hT z a b]
        _ = T.P.M (false, S.LA z) a * T.P.M (false, S.LA z) a *
              (T.P.M (true, S.LB z) b * T.P.M (true, S.LB z) b) := by noncomm_ring
        _ = T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b := by rw [hP, hQ]
    · simp
    · simp
    · simp [T.P.projective]
    · simp
    · simp [T.P.projective]
  normalized := by
    rintro ⟨r, z⟩
    cases r
    · rw [OAns.sum_eq]
      simp only [oracleOp_oracle_pair, oracleOp_oracle_single, Finset.sum_const_zero, add_zero]
      rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, T.P.normalized, T.P.normalized, one_mul]
    · rw [OAns.sum_eq]
      simp only [oracleOp_alice_pair, oracleOp_alice_single, Finset.sum_const_zero, zero_add]
      exact T.P.normalized _
    · rw [OAns.sum_eq]
      simp only [oracleOp_bob_pair, oracleOp_bob_single, Finset.sum_const_zero, zero_add]
      exact T.P.normalized _

@[simp] theorem oracleMeas_M (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleMeas T hT).M = S.oracleOp T := rfl

/-! ## The support of the oracularized question distribution

Two questions of positive weight come from one seed. Everything the case analysis below needs
about `oDist` is in these two lemmas: equal roles force equal questions, so orthogonality is
available at a repeated question, and an oracle paired with an isolated player is paired with
*that player's own* question. -/

/-! ## Rejected answers are zero operators

The honest oracle's operator at a pair the original predicate rejects is not merely
improbable: it is `0`. This is where faithfulness of the normalized trace
(`SyncStrategy.eq_zero_of_trace_re_eq_zero`) earns its keep, and it is what makes the case
analysis of the decider's seven checks short. -/

/-! ## The two consistency checks

An oracle's component for a player's role and that player's own answer are measured by
operators at the *same* question of the doubled game, so orthogonality applies once the
oracle's other factor has been commuted out of the way. -/

/-! ## The honest oracularized strategy, and its value

`fig:oracle-decider` runs seven checks, and each one that can fail makes one of the two
operators, or their product, zero: a shape mismatch and a rejected oracle pair by
`oracleOp_eq_zero_of_shapeOk` and `oracleOp_eq_zero_of_gameCheck`, check 2(a) by orthogonality
at a repeated question (which the support lemma makes available), and check 2(b) by the two
lemmas above. So the strategy never produces a rejected outcome, and
`MIPRE.tracialValue_eq_one_of_re_eq_zero` turns that into value `1`. -/

variable (S)

/-- The honest strategy for the oracularized game: the same Hilbert space as the input
strategy, the joint measurement for an oracle, and the input strategy's own measurement for an
isolated player. -/
noncomputable def oracleStrategy (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    SyncStrategy S.oracular where
  d := T.d
  d_pos := T.d_pos
  P := S.oracleMeas T hT

variable {S}

@[simp] theorem oracleStrategy_d (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) :
    (S.oracleStrategy T hT).d = T.d := rfl

/-! ## The honest strategy is PCC

Every honest operator at seed `z` is a product of factors drawn from the four atoms
`M^{(\mathsf{false}, L^𝖠 z)}_a` and `M^{(\mathsf{true}, L^𝖡 z)}_b`, and those atoms commute
pairwise: two at one question because distinct outcomes are orthogonal
(`SyncStrategy.orthogonal`) and equal ones are equal, and one of each because the input
strategy is PCC. So the case analysis is `Commute.mul_left` and `Commute.mul_right` over the
nine role pairs. -/

end SeededGame

end MIPRE


