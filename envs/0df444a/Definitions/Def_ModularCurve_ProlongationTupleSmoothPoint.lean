-- Prove2me | Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
-- name    : ModularCurve_ProlongationTupleSmoothPoint
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/5d332291-cf8e-5696-a0bb-7da281caf6b0
-- title:
--   Smooth-point local rings on the two copies at level N
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $N\ge 1$, $k$ a field of characteristic $q$ with a ring homomorphism $\mathrm{red}\colon A\to k$, and `data`, `hKr`, `hα`, `hβ` the modular polynomial data with its Kronecker congruence and the two Hecke integrality hypotheses; $P$ is a place specialisation `PlaceSpecialization A q N data hKr k red hα hβ`, which attaches to each place $W$ of $\overline{\mathbb Q}\cdot F_{Nq}$ two places `P.reduceFst W`, `P.reduceSnd W` of `modularFunctionFieldC k N` (obtained by restricting $W$ along `heckeAlphaBar`, resp. `heckeBetaBar`, and specialising by `P.sp`) together with the strictness predicates `P.IsStrictFst`, `P.IsStrictSnd`; and $R$ is a `ProlongationTuple P`, whose fields include two regular prolongations `R.R₁`, `R.R₂` of $A$ to `modularFunctionFieldBar (N * q)` with residue field the level-$N$ function field over the residue field of $A$.
--
--   For a place $v$ of `modularFunctionFieldC k N`, `smoothLocalRingFst R v` is the subring of `modularFunctionFieldBar (N * q)` given by the intersection of the valuation ring `R.R₁.integers` with the infimum of the valuation rings of all places $W$ satisfying `P.IsStrictFst W` and `P.reduceFst W = v`; `smoothLocalRingSnd R v` is the analogous intersection of `R.R₂.integers` with the valuation rings of the $W$ satisfying `P.IsStrictSnd W` and `P.reduceSnd W = v`. The accompanying lemmas record the membership criteria in this unfolded form — $r$ lies in `smoothLocalRingFst R v` exactly when $r\in$ `R.R₁.integers` and $r$ lies in the valuation ring of every strict place of the first kind reducing to $v$, and symmetrically for the second — together with the two projections of each criterion. Nothing is assumed about $v$: when no strict place of the relevant kind reduces to $v$, the infimum is empty and the ring is just `R.R₁.integers`, resp. `R.R₂.integers`.
--
--   **Relation to Mathlib.** The intersection is formed in Mathlib's lattice of subrings, with `ValuationSubring.toSubring` used to view valuation rings as subrings; the notions of place, regular prolongation and prolongation tuple entering the definition are the project's own.
--
--   **Where it is used.** These rings serve as valuation-theoretic stand-ins for the local rings of a model of $X_0(Nq)$ over $A$ at a smooth point of the first, resp. second, copy of $X_0(N)$ in the characteristic-$q$ fibre, and underlie the statements about residue discs, parameters and $t$-expansions used in the analysis of that fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ProlongationTupleSmoothPoint.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve

namespace ModularCurve

namespace PlaceSpecialization

namespace ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

def smoothLocalRingFst (R : ProlongationTuple P) (v : Place k (modularFunctionFieldC k N)) :
    Subring (modularFunctionFieldBar (N * q)) :=
  R.R₁.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) //
            P.IsStrictFst W ∧ P.reduceFst W = v},
      (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).toValuationSubring.toSubring

def smoothLocalRingSnd (R : ProlongationTuple P) (v : Place k (modularFunctionFieldC k N)) :
    Subring (modularFunctionFieldBar (N * q)) :=
  R.R₂.integers.toSubring ⊓
    ⨅ W : {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) //
            P.IsStrictSnd W ∧ P.reduceSnd W = v},
      (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).toValuationSubring.toSubring

variable (R : ProlongationTuple P)

theorem mem_smoothLocalRingFst_iff (v : Place k (modularFunctionFieldC k N))
    (r : modularFunctionFieldBar (N * q)) :
    r ∈ R.smoothLocalRingFst v ↔
      r ∈ R.R₁.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.IsStrictFst W → P.reduceFst W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingFst, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_smoothLocalRingSnd_iff (v : Place k (modularFunctionFieldC k N))
    (r : modularFunctionFieldBar (N * q)) :
    r ∈ R.smoothLocalRingSnd v ↔
      r ∈ R.R₂.integers ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.IsStrictSnd W → P.reduceSnd W = v → r ∈ W.toValuationSubring := by
  simp only [smoothLocalRingSnd, Subring.mem_inf, Subring.mem_iInf, Subtype.forall, and_imp]
  rfl

theorem mem_integers_of_mem_smoothLocalRingFst {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingFst v) : r ∈ R.R₁.integers :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).1

theorem mem_integers_of_mem_smoothLocalRingSnd {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingSnd v) : r ∈ R.R₂.integers :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).1

theorem mem_toValuationSubring_of_mem_smoothLocalRingFst {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingFst v)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictFst W) (hv : P.reduceFst W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingFst_iff v r).mp h).2 W hW hv

theorem mem_toValuationSubring_of_mem_smoothLocalRingSnd {v : Place k (modularFunctionFieldC k N)}
    {r : modularFunctionFieldBar (N * q)} (h : r ∈ R.smoothLocalRingSnd v)
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hW : P.IsStrictSnd W) (hv : P.reduceSnd W = v) : r ∈ W.toValuationSubring :=
  ((R.mem_smoothLocalRingSnd_iff v r).mp h).2 W hW hv

end ProlongationTuple

end PlaceSpecialization

end ModularCurve

end


