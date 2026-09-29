-- Prove2me | Definitions.Def_ModularCurve_SmoothPointLocalRing
-- name    : ModularCurve_SmoothPointLocalRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/7d8dac65-4956-53fa-a849-b2b0106580be
-- title:
--   Smooth-point local rings for level-one prolongation pairs
-- statement:
--   The standing context is a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with a ring map $\mathrm{red}\colon A\to k$, modular polynomial data for $q$ with a Kronecker congruence, integrality hypotheses for the two Hecke degeneracy maps at level $1$, and a place specialisation $P$ of this data. For a level-one prolongation pair $R$ for $P$ — a structure whose fields include two regular prolongations $R_1,R_2$ of $A$ to the base-changed full modular function field $F=$ `modularFunctionFieldBar (1 * q)` with residue field the level-one function field over the residue field of $A$, together with the Fricke compatibility relating them — two subrings of $F$ are defined, indexed by a place $v$ of the level-one function field `modularFunctionFieldC k 1` over $k$.
--
--   The first, `smoothLocalRingFst R v`, is the intersection of the valuation subring $R_1$.`integers` with the infimum, taken in the lattice of subrings of $F$, of the valuation subrings $\mathcal O_W$ of all places $W$ of $F$ over $\overline{\mathbb Q}$ satisfying `P.IsStrictTypeOne W` and `P.redFst W = v`; here `redFst W` is the place obtained by restricting $W$ along the first Hecke embedding and applying the specialisation map of $P$, `redSnd` likewise along the second, and strict type one means that geometric-level Frobenius carries `redFst W` to `redSnd W` while its square does not fix `redFst W`. The second, `smoothLocalRingSnd R v`, is the analogue with $R_2$, strict type two (`redFst W` is the Frobenius image of `redSnd W`, and the square of Frobenius does not fix `redSnd W`) and the condition `P.redSnd W = v`.
--
--   The remaining declarations are the two membership criteria, stating that lying in these subrings is exactly $R_i$-integrality together with integrality at every relevant place $W$, and the corresponding one-sided projections extracting each conjunct.
--
--   **Relation to Mathlib.** The intersections are formed in Mathlib's lattice of subrings and use Mathlib's `ValuationSubring`; the notions of place of a function field, regular prolongation, place specialisation and the modular function fields are the project's own.
--
--   **Where it is used.** These subrings serve as valuation-theoretic substitutes for the local rings at smooth points of the two components of the reduction of $X_0(q)$ modulo $q$, on which the local expansion arguments for the reduction of $J_0(q)$ at $q$ are carried out; those arguments feed the level-lowering step of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SmoothPointLocalRing.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

namespace LevelOneProlongationPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

def smoothLocalRingFst (R : LevelOneProlongationPair P) (v : Place k ↥(modularFunctionFieldC k 1)) :
    Subring ↥(modularFunctionFieldBar (1 * q)) :=
  R.R₁.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) //
            P.IsStrictTypeOne W ∧ P.redFst W = v},
      (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).toValuationSubring.toSubring

def smoothLocalRingSnd (R : LevelOneProlongationPair P) (v : Place k ↥(modularFunctionFieldC k 1)) :
    Subring ↥(modularFunctionFieldBar (1 * q)) :=
  R.R₂.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) //
            P.IsStrictTypeTwo W ∧ P.redSnd W = v},
      (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).toValuationSubring.toSubring

variable (R : LevelOneProlongationPair P)

theorem mem_smoothLocalRingFst_iff (v : Place k ↥(modularFunctionFieldC k 1)) (r : ↥(modularFunctionFieldBar (1 * q))) :
    r ∈ R.smoothLocalRingFst v ↔
      r ∈ R.R₁.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.IsStrictTypeOne W → P.redFst W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingFst, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_smoothLocalRingSnd_iff (v : Place k ↥(modularFunctionFieldC k 1)) (r : ↥(modularFunctionFieldBar (1 * q))) :
    r ∈ R.smoothLocalRingSnd v ↔
      r ∈ R.R₂.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.IsStrictTypeTwo W → P.redSnd W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingSnd, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_integers_of_mem_smoothLocalRingFst {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingFst v) : r ∈ R.R₁.integers :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).1

theorem mem_integers_of_mem_smoothLocalRingSnd {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingSnd v) : r ∈ R.R₂.integers :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).1

theorem mem_toValuationSubring_of_mem_smoothLocalRingFst {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingFst v) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsStrictTypeOne W) (hv : P.redFst W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).2 W hW hv

theorem mem_toValuationSubring_of_mem_smoothLocalRingSnd {v : Place k ↥(modularFunctionFieldC k 1)} {r : ↥(modularFunctionFieldBar (1 * q))}
    (h : r ∈ R.smoothLocalRingSnd v) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsStrictTypeTwo W) (hv : P.redSnd W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).2 W hW hv

end LevelOneProlongationPair

end PlaceSpecialization

end ModularCurve

end


