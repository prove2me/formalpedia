-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularGame
-- name    : MIPRE_Foundations_OracularGame
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:28.812193+00:00
-- url     : https://prove2.me/theorems/74077abe-b6ef-4324-a6ad-79efe6122c7f
-- title:
--   Definitions of OracularGame: Oracularization, at the level of games Blueprint `thm:oracularization` (paper `oracularization.tex`, `sec:orac-def` and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Oracularization, at the level of games. Blueprint `thm:oracularization` (paper `oracularization.tex`, `sec:orac-def` and `fig:oracle-decider`) turns a normal form verifier into one where a single player --- the *oracle* --- receives the sampler's whole seed and answers *both* original questions, while the other player receives one of the two questions and must answer consistently. That makes the predicate a pointwise function of one player's answer, which is the format answer reduction needs. This file is the construction and its question distribution, at the level of games: no samplers, no…
--
--   **Definitions** (17): `MIPRE.OAns` (Answers of the oracularized game: a pair, from an oracle, or a single answer, from an isolated player.); `MIPRE.OAns.equivSum` (`OAns A` as a sum type.); `MIPRE.Role` (The three roles of the oracularized game: the oracle, who answers both original questions, and the two isolated players.); `MIPRE.SeededGame` (A **seeded game**: the question pair is `(L^𝖠 z, L^𝖡 z)` for a seed `z` drawn uniformly from a finite space, and the predicate is read off…); `MIPRE.SeededGame.dist` (The question distribution of the input game: the law of `(L^𝖠 z, L^𝖡 z)`.); `MIPRE.SeededGame.gameCheck` (The **game check**, step 1: an oracle's pair of answers must be accepted by the original predicate at the pair of questions its seed…); `MIPRE.SeededGame.oDist` (The uniform distribution over the oracularized game's random choices: the ordered pair of roles and the seed.); `MIPRE.SeededGame.oaccepts` (The predicate of `fig:oracle-decider`: the shape checks, the game check for each oracle, and the two consistency checks --- equal roles…); `MIPRE.SeededGame.oquestion` (The question a player in role `r` receives on seed `z`: the oracle gets the seed itself, an isolated player the question the corresponding…); `MIPRE.SeededGame.oracleVsPlayer` (Check 2(b): an oracle's component for the other player's role must match that player's answer.); `MIPRE.SeededGame.oracular` (**The oracularized game** (blueprint `thm:oracularization`, paper `sec:orac-def`).); and -3 more.
--
--   **Embedded lemmas** (13): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `dist_nonneg`, `oDist_nonneg`, `oaccepts_eq_false_of_ne`, `oquestion_alice`, `oquestion_bob`, `oquestion_fst`, `oquestion_oracle`, `oracular_D`, `oracular_μ`, `sum_dist`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularGame` (`MIPRE/Foundations/OracularGame.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularGame.lean; blueprint def:oracular-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularGame.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Oracularization, at the level of games

Blueprint `thm:oracularization` (paper `oracularization.tex`, `sec:orac-def` and
`fig:oracle-decider`) turns a normal form verifier into one where a single player --- the
*oracle* --- receives the sampler's whole seed and answers *both* original questions, while the
other player receives one of the two questions and must answer consistently. That makes the
predicate a pointwise function of one player's answer, which is the format answer reduction
needs.

This file is the construction and its question distribution, at the level of games: no
samplers, no deciders, no types-as-Turing-machine-strings. What oracularization uses of a
sampler is only the pair of maps `L^𝖠, L^𝖡` on the seed space, so the input here is a
`SeededGame`: a finite seed space, two question maps, and a decision predicate. The original
game is the law of `(L^𝖠 z, L^𝖡 z)` for a uniform seed, the paper's CL distribution
(`MIPRE.CL.clDist` is the same thing for `V = 𝔽^ι`).

The output `SeededGame.oracular` is a `SynchronousGame` on questions `Role × V` and answers
`OAns A`, and its synchronicity is not an extra hypothesis: equal questions have equal roles,
and check 2(a) of `fig:oracle-decider` rejects unequal answers there.

## Scope, and what this file does not do

Two of the four repairs `rem:oracularization-repairs` records are about the *verifier*, not the
game, and are untouched here: grouping the decider's failed bounded parses into one
distinguished outcome (so the oracle families are projective measurements rather than
sub-measurements), and the truncation of answers to `B_𝒟(n)`. At a finite game-level answer
alphabet there is no parse to fail, so there is nothing to group; saying so is more honest than
claiming the repair is discharged. What *is* modelled is the shape check: an answer whose shape
does not match the player's role is rejected (`shapeOk`), which is the game-level residue of
the parse.

Completeness --- a value-`1` PCC strategy for the input gives one for the output, with
*identical measurement operators* rather than a symmetric state, which is repair 2 --- and
soundness, with its single square root, are separate pieces.
-/

namespace MIPRE

open Finset

/-! ## Roles -/

/-- The three roles of the oracularized game: the oracle, who answers both original
questions, and the two isolated players. -/
inductive Role
  | oracle
  | alice
  | bob
  deriving DecidableEq

instance : Fintype Role where
  elems := {Role.oracle, Role.alice, Role.bob}
  complete r := by cases r <;> simp

instance : Inhabited Role := ⟨Role.oracle⟩

/-! ## Seeded games -/

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- A **seeded game**: the question pair is `(L^𝖠 z, L^𝖡 z)` for a seed `z` drawn uniformly
from a finite space, and the predicate is read off the questions and answers. This is
everything oracularization uses of a normal form verifier's sampler. -/
structure SeededGame (V A : Type*) where
  /-- Alice's question map. -/
  LA : V → V
  /-- Bob's question map. -/
  LB : V → V
  /-- The decision predicate of the original game. -/
  D : V → V → A → A → Bool

namespace SeededGame

variable (S : SeededGame V A)

/-- The question distribution of the input game: the law of `(L^𝖠 z, L^𝖡 z)`. -/
noncomputable def dist (x y : V) : ℝ :=
  ((univ.filter fun z => S.LA z = x ∧ S.LB z = y).card : ℝ) / Fintype.card V

omit [Fintype A] [DecidableEq A] in
theorem dist_nonneg (x y : V) : 0 ≤ S.dist x y :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype A] [DecidableEq A] in
theorem sum_dist [Nonempty V] : ∑ x, ∑ y, S.dist x y = 1 := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have key : ∑ p : V × V, ((univ.filter fun z => S.LA z = p.1 ∧ S.LB z = p.2).card : ℝ)
      = Fintype.card V := by
    rw [← Nat.cast_sum, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := fun z => (S.LA z, S.LB z)) (t := univ) (fun _ _ => mem_univ _)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    ext z
    simp [Prod.ext_iff]
  rw [← Fintype.sum_prod_type' fun x y => S.dist x y]
  simp only [dist, div_eq_mul_inv, ← Finset.sum_mul, key, mul_inv_cancel₀ hcard.ne']

/-- The input game itself. -/
noncomputable def toGame [Nonempty V] : Game V V A A where
  μ := S.dist
  μ_nonneg := S.dist_nonneg
  μ_sum_one := S.sum_dist
  D := S.D

omit [DecidableEq A] in
@[simp] theorem toGame_μ [Nonempty V] : S.toGame.μ = S.dist := rfl

omit [DecidableEq A] in
@[simp] theorem toGame_D [Nonempty V] : S.toGame.D = S.D := rfl

end SeededGame

/-! ## The oracularized alphabets -/

/-- Answers of the oracularized game: a pair, from an oracle, or a single answer, from an
isolated player. An answer whose shape does not match the role is rejected. -/
inductive OAns (A : Type*)
  | pair (a b : A)
  | single (a : A)
  deriving DecidableEq

/-- `OAns A` as a sum type. The `Fintype` instance goes through this rather than through a
union of images, so that a sum over `OAns A` splits into the two blocks (`OAns.sum_eq`), which
is what the measurement's normalization needs. -/
def OAns.equivSum : OAns A ≃ (A × A) ⊕ A where
  toFun
    | .pair a b => .inl (a, b)
    | .single a => .inr a
  invFun
    | .inl (a, b) => .pair a b
    | .inr a => .single a
  left_inv u := by cases u <;> rfl
  right_inv x := by rcases x with ⟨a, b⟩ | a <;> rfl

instance : Fintype (OAns A) := Fintype.ofEquiv _ (OAns.equivSum (A := A)).symm

instance [Inhabited A] : Inhabited (OAns A) := ⟨OAns.single default⟩

namespace SeededGame

variable (S : SeededGame V A)

/-- The question a player in role `r` receives on seed `z`: the oracle gets the seed itself,
an isolated player the question the corresponding original player would have received. -/
def oquestion : Role → V → Role × V
  | .oracle, z => (.oracle, z)
  | .alice, z => (.alice, S.LA z)
  | .bob, z => (.bob, S.LB z)

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] in
@[simp] theorem oquestion_fst (r : Role) (z : V) : (S.oquestion r z).1 = r := by
  cases r <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] in
@[simp] theorem oquestion_oracle (z : V) : S.oquestion .oracle z = (.oracle, z) := rfl

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] in
@[simp] theorem oquestion_alice (z : V) : S.oquestion .alice z = (.alice, S.LA z) := rfl

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] in
@[simp] theorem oquestion_bob (z : V) : S.oquestion .bob z = (.bob, S.LB z) := rfl

/-! ## The decision predicate of `fig:oracle-decider` -/

/-- The shape check: an oracle answers a pair, an isolated player a single answer. -/
def shapeOk : Role → OAns A → Bool
  | .oracle, .pair _ _ => true
  | .alice, .single _ => true
  | .bob, .single _ => true
  | _, _ => false

/-- The **game check**, step 1: an oracle's pair of answers must be accepted by the original
predicate at the pair of questions its seed determines. -/
def gameCheck : Role × V → OAns A → Bool
  | (.oracle, z), .pair a b => S.D (S.LA z) (S.LB z) a b
  | _, _ => true

/-- Check 2(b): an oracle's component for the other player's role must match that player's
answer. -/
def oracleVsPlayer : Role × V → Role × V → OAns A → OAns A → Bool
  | (.oracle, _), (.alice, _), .pair a _, .single a' => decide (a = a')
  | (.oracle, _), (.bob, _), .pair _ b, .single b' => decide (b = b')
  | _, _, _, _ => true

/-- The predicate of `fig:oracle-decider`: the shape checks, the game check for each oracle,
and the two consistency checks --- equal roles force equal answers, and an oracle's relevant
component must match an isolated player's answer. -/
def oaccepts (p q : Role × V) (u v : OAns A) : Bool :=
  shapeOk p.1 u && shapeOk q.1 v && S.gameCheck p u && S.gameCheck q v
    && (if p.1 = q.1 then decide (u = v) else true)
    && oracleVsPlayer p q u v && oracleVsPlayer q p v u

omit [Fintype V] [DecidableEq V] [Fintype A] in
theorem oaccepts_eq_false_of_ne {p : Role × V} {u v : OAns A} (h : u ≠ v) :
    S.oaccepts p p u v = false := by
  simp [oaccepts, h]

/-! ## The oracularized game -/

/-- The uniform distribution over the oracularized game's random choices: the ordered pair of
roles and the seed. -/
noncomputable def oDist (p q : Role × V) : ℝ :=
  ∑ s : Role × Role × V, (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
    if (S.oquestion s.1 s.2.2, S.oquestion s.2.1 s.2.2) = (p, q) then 1 else 0

omit [Fintype A] [DecidableEq A] in
theorem oDist_nonneg (p q : Role × V) : 0 ≤ S.oDist p q :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (by split_ifs <;> norm_num)

omit [Fintype A] [DecidableEq A] in
theorem sum_oDist [Nonempty V] : ∑ p, ∑ q, S.oDist p q = 1 := by
  have hpos : 0 < Fintype.card (Role × Role × V) :=
    Fintype.card_pos_iff.mpr ⟨(default, default, Classical.arbitrary V)⟩
  simp only [oDist]
  rw [← Fintype.sum_prod_type', Finset.sum_comm]
  simp only [← Finset.mul_sum, Prod.mk.eta, Fintype.sum_ite_eq, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

/-- **The oracularized game** (blueprint `thm:oracularization`, paper `sec:orac-def`). It is
synchronous with no further hypothesis: equal questions carry equal roles, and check 2(a)
rejects unequal answers there. -/
noncomputable def oracular [Nonempty V] : SynchronousGame (Role × V) (OAns A) where
  μ := S.oDist
  μ_nonneg := S.oDist_nonneg
  μ_sum_one := S.sum_oDist
  D := S.oaccepts
  synchronous _ _ _ h := S.oaccepts_eq_false_of_ne h

@[simp] theorem oracular_μ [Nonempty V] : S.oracular.μ = S.oDist := rfl

@[simp] theorem oracular_D [Nonempty V] : S.oracular.D = S.oaccepts := rfl

end SeededGame

end MIPRE


