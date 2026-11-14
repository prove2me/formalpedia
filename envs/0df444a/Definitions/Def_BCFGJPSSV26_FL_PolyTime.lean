-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_PolyTime
-- name    : BCFGJPSSV26_FL_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:15:09.526599+00:00
-- url     : https://prove2.me/theorems/840a9b8d-0482-4b73-8eea-aa29668713cb
-- title:
--   BCFGJPSSV26.FL.PolyTime — The algorithm of Theorem 1.4 runs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.FL.PolyTime` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.FL.alg_polytime`: the algorithm `BCFGJPSSV26.FL.alg` on an encoded instance and an
--   opening cost is computable in polynomial time. As for the core of Theorem 1.2
--   (`BCFGJPSSV26.Greedy.core_polytime`), the greedy run loops over all clients and all facilities,
--   so it is certified on tuples with `n` and `m` in unary (`BCFGJPSSV26.FL.PT.encIn`), to which the
--   encoding of an instance converts in polynomial time (an instance has `n + m` rows).
--
--   Every parameter of the run is a fixed composition of polynomial-time operations on the input:
--   the least positive distance, the scale `t`, the scaled table, the bound `M`, the number
--   `R = O(log (n M))` of phases (in unary), the cap `K = 2 (1 + ε²)^R` and the grid exponent `Pu`.
--   CompleteSolution is then certified by `BCFGJPSSV26.FL.PT.completeG`, the trivial solution by
--   `BCFGJPSSV26.Greedy.PT.trivialSolL`, and the objectives by `BCFGJPSSV26.Combine.costQ_polytime`.
--
--   **Contents.** The module is published as a whole: 25 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.FL.alg_polytime` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_PolyTime`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/PolyTime.lean

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_PolyTimeCtx
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm of Theorem 1.4 runs in polynomial time

`BCFGJPSSV26.FL.alg_polytime`: the algorithm `BCFGJPSSV26.FL.alg` on an encoded instance and an
opening cost is computable in polynomial time. As for the core of Theorem 1.2
(`BCFGJPSSV26.Greedy.core_polytime`), the greedy run loops over all clients and all facilities,
so it is certified on tuples with `n` and `m` in unary (`BCFGJPSSV26.FL.PT.encIn`), to which the
encoding of an instance converts in polynomial time (an instance has `n + m` rows).

Every parameter of the run is a fixed composition of polynomial-time operations on the input:
the least positive distance, the scale `t`, the scaled table, the bound `M`, the number
`R = O(log (n M))` of phases (in unary), the cap `K = 2 (1 + ε²)^R` and the grid exponent `Pu`.
CompleteSolution is then certified by `BCFGJPSSV26.FL.PT.completeG`, the trivial solution by
`BCFGJPSSV26.Greedy.PT.trivialSolL`, and the objectives by `BCFGJPSSV26.Combine.costQ_polytime`.
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Greedy Greedy.PT

namespace PT

/-- Inputs of the algorithm: the tuple of an instance, with `n` and `m` in unary, and the opening
cost. -/
abbrev encIn : Raw × ℚ ↪ List Bool := encPair encCI encRat

theorem xR : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1) encIn encRaw :=
  ((toBin (fst _ _)).prod ((toBin ((fst _ _).comp (snd _ _))).prod
    ((snd _ _).comp (snd _ _)))).comp (fst _ _)

theorem nU : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.n) encIn encUnary :=
  (fst _ _).comp (fst _ _)

theorem mU : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.m) encIn encUnary :=
  ((fst _ _).comp (snd _ _)).comp (fst _ _)

theorem fQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.2) encIn encRat := snd _ _

theorem nQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ (p.1.n : ℚ)) encIn encRat :=
  rat_natCast' (toBin nU)

theorem dminQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ dminFL p.1) encIn encRat :=
  Combine.minQ_polytime (guessesL xR)

theorem tQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ tFL p.1 p.2) encIn encRat :=
  rat_min' (rat_div' dminQ (rat_mul' (const cS) nQ)) fQ

theorem fhatQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ fhatFL p.1 p.2) encIn encRat :=
  rat_div' (rat_mul' (const (lmpC * (1 - δ0))) fQ) tQ

theorem dMaxQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ p.1.dMaxQ) encIn encRat :=
  rat_add' (const 1) (rat_sum' (mapWithInput (f := fun _ (row : List ℚ) ↦ row.sum) (rawTL xR)
    (rat_sum' (snd _ _))))

theorem MQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ MFL p.1 p.2) encIn encRat :=
  rat_add' (rat_add' (rat_div' dMaxQ tQ) (const 1)) fhatQ

theorem ηQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ ηFL p.1.n) encIn encRat :=
  rat_div' (const _) (rat_mul' (const 100) (rat_sq' nQ))

theorem RU : ComputableInPolyTime (fun p : Raw × ℚ ↦ RFL p.1 p.2) encIn encUnary :=
  unary_add' (unary_mul' (const _) (clogU (natCeil (rat_mul' (rat_mul' (const 5) nQ) MQ))))
    (const 1)

theorem KQ : ComputableInPolyTime (fun p : Raw × ℚ ↦ KFL p.1 p.2) encIn encRat :=
  rat_mul' (const 2) (ratPow (const _) RU)

theorem PuU : ComputableInPolyTime (fun p : Raw × ℚ ↦ Nat.clog 2 ⌈KFL p.1 p.2 / ηFL p.1.n⌉₊)
    encIn encUnary :=
  clogU (natCeil (rat_div' KQ ηQ))

theorem stabL : ComputableInPolyTime (fun p : Raw × ℚ ↦ stabFL p.1 p.2) encIn
    (encList (encList encRat)) := by
  unfold stabFL
  have hentry : ComputableInPolyTime (fun r : ((Raw × ℚ) × ℕ) × ℕ ↦
      r.1.1.1.fdist r.1.2 r.2 / tFL r.1.1.1 r.1.1.2 + 1)
      (encPair (encPair encIn encUnary) encUnary) encRat :=
    rat_add' (rat_div' (fdistQ (xR.comp ((fst _ _).comp (fst _ _)))
      (toBin ((snd _ _).comp (fst _ _))) (toBin (snd _ _)))
      (tQ.comp ((fst _ _).comp (fst _ _)))) (const 1)
  have hrow := mapWithInput (f := fun (q : (Raw × ℚ) × ℕ) (i : ℕ) ↦
    q.1.1.fdist q.2 i / tFL q.1.1 q.1.2 + 1) (unary_range' (mU.comp (fst _ _))) hentry
  exact mapWithInput (f := fun (p : Raw × ℚ) (j : ℕ) ↦
    (List.range p.1.m).map fun i ↦ p.1.fdist j i / tFL p.1 p.2 + 1) (unary_range' nU) hrow

/-- **The fields of the context of the greedy run** are computable in polynomial time. -/
theorem ctxPT : CtxPT encIn (fun p : Raw × ℚ ↦ ctxFL p.1 p.2) :=
  ⟨nU, mU, stabL, const δ0, const ε0, KQ, RU, PuU, unary_add' mU (const 4)⟩

theorem runL : ComputableInPolyTime (fun p : Raw × ℚ ↦ runFL p.1 p.2) encIn (encList encNat) := by
  unfold runFL toCenters
  have hH : ComputableInPolyTime (fun p : Raw × ℚ ↦ (ctxFL p.1 p.2).complete (fhatFL p.1 p.2) [])
      encIn encSl := completeG ctxPT fhatQ (const [])
  exact eraseDupsByWithInput (r := fun _ i j ↦ i == j)
    (mapWithInput (f := fun _ (a : AAtom) ↦ a.1) (flattenS hH) ((fst _ _).comp (snd _ _)))
    (beq ((snd _ _).comp (fst _ _)) (snd _ _))

theorem scoreQ {S : Raw × ℚ → List ℕ} (hS : ComputableInPolyTime S encIn (encList encNat)) :
    ComputableInPolyTime (fun p : Raw × ℚ ↦ score p.1 p.2 (S p)) encIn encRat :=
  rat_add' (Combine.costQ_polytime (rawNB xR) (rawTL xR) hS)
    (rat_mul' (rat_mul' (const lmpC) fQ) (rat_natCast' (toBin (lenL hS))))

theorem algL : ComputableInPolyTime (fun p : Raw × ℚ ↦ alg p.1 p.2) encIn (encList encNat) := by
  unfold alg
  have hT := trivialSolL xR
  exact ite' (bool_and' (Combine.valid_polytime (rawMB xR) (rawMB xR) runL)
    (rat_lt' (scoreQ runL) (scoreQ hT))) runL hT

/-! ### From the encoding of an instance -/

theorem toRaw_polytime : ComputableInPolyTime toRaw encInstance encRaw :=
  of_eq fun I ↦ (encInstance_eq I).symm

theorem m_le_length (I : Instance) : I.m ≤ (encInstance I).length := by
  have h : (distTable I).length ≤
      (Encoding.encList (Encoding.encList encRat) (distTable I)).length :=
    length_le_length_encList _ _
  have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
  rw [Combine.length_encInstance]
  omega

/-- The tuple of an instance, with `n` and `m` in unary. -/
theorem toRawU_polytime : ComputableInPolyTime toRaw encInstance encCI :=
  (binary_to_unary_bounded ((fst _ _).comp toRaw_polytime) (encoding_length encInstance)
    fun I ↦ Combine.n_le_length I).prod
  ((binary_to_unary_bounded (((fst _ _).comp (snd _ _)).comp toRaw_polytime)
    (encoding_length encInstance) m_le_length).prod
    ((((fst _ _).comp (snd _ _)).comp (snd _ _)).comp toRaw_polytime |>.prod
      ((((snd _ _).comp (snd _ _)).comp (snd _ _)).comp toRaw_polytime)))

theorem pairU_polytime : ComputableInPolyTime (fun p : Instance × ℚ ↦ (toRaw p.1, p.2))
    (encPair encInstance encRat) encIn :=
  (toRawU_polytime.comp (fst _ _)).prod (snd _ _)

theorem algU_polytime : ComputableInPolyTime
    (fun p : Instance × ℚ ↦ alg (toRaw p.1, p.2).1 (toRaw p.1, p.2).2)
    (encPair encInstance encRat) (encList encNat) :=
  algL.comp pairU_polytime

end PT

end BCFGJPSSV26.FL


