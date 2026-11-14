-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_PolyTimeCtx
-- name    : BCFGJPSSV26_FL_PolyTimeCtx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:08:12.455191+00:00
-- url     : https://prove2.me/theorems/482a1b77-7494-45b6-b4e1-f16071656218
-- title:
--   BCFGJPSSV26.FL.PolyTimeCtx — Polynomial time of CompleteSolution for computed parameters
-- statement:
--   This is module `BCFGJPSSV26.FL.PolyTimeCtx` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The certificates of `Greedy/PolyTime/AuxCtx.lean` and `Greedy/PolyTime/AuxComplete.lean` are
--   stated for the context `BCFGJPSSV26.Greedy.ctx c x` of a core input, whose parameters are those
--   of `BCFGJPSSV26.Greedy.ipar`. The greedy run of Theorem 1.4 uses other parameters
--   (`BCFGJPSSV26.FL.iparFL`). Here are the same certificates for any context `C a` computed from an
--   input `a`, given certificates for the fields that the tests, the profiles and CompleteSolution read
--   (`BCFGJPSSV26.FL.PT.CtxPT`): `n`, `m`, `R`, `Pu` and `L` in unary, `δ`, `ε` and `K`, and the
--   table. The proofs are those of the two files, with these certificates in place of the ones of the
--   parameters of `BCFGJPSSV26.Greedy.ipar`.
--
--   **Contents.** The module is published as a whole: 29 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_PolyTimeCtx`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/PolyTimeCtx.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxComplete

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.PolyTimeCtx` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of CompleteSolution for computed parameters

The certificates of `Greedy/PolyTime/AuxCtx.lean` and `Greedy/PolyTime/AuxComplete.lean` are
stated for the context `BCFGJPSSV26.Greedy.ctx c x` of a core input, whose parameters are those
of `BCFGJPSSV26.Greedy.ipar`. The greedy run of Theorem 1.4 uses other parameters
(`BCFGJPSSV26.FL.iparFL`). Here are the same certificates for any context `C a` computed from an
input `a`, given certificates for the fields that the tests, the profiles and CompleteSolution read
(`BCFGJPSSV26.FL.PT.CtxPT`): `n`, `m`, `R`, `Pu` and `L` in unary, `δ`, `ε` and `K`, and the
table. The proofs are those of the two files, with these certificates in place of the ones of the
parameters of `BCFGJPSSV26.Greedy.ipar`.
-/

@[expose] public section

namespace BCFGJPSSV26.FL.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Greedy Greedy.PT

/-- **Certificates for the fields of a computed context** that the tests, the profiles and
CompleteSolution read. -/
structure CtxPT {α : Type} (input : α ↪ List Bool) (C : α → Ctx) : Prop where
  n : ComputableInPolyTime (fun a ↦ (C a).ip.n) input encUnary
  m : ComputableInPolyTime (fun a ↦ (C a).ip.m) input encUnary
  tab : ComputableInPolyTime (fun a ↦ (C a).tab) input (encList (encList encRat))
  δ : ComputableInPolyTime (fun a ↦ (C a).ip.δ) input encRat
  ε : ComputableInPolyTime (fun a ↦ (C a).ip.ε) input encRat
  K : ComputableInPolyTime (fun a ↦ (C a).ip.K) input encRat
  R : ComputableInPolyTime (fun a ↦ (C a).ip.R) input encUnary
  Pu : ComputableInPolyTime (fun a ↦ (C a).ip.Pu) input encUnary
  L : ComputableInPolyTime (fun a ↦ (C a).ip.L) input encUnary

variable {α : Type} {input : α ↪ List Bool} {C : α → Ctx}

theorem CtxPT.comp {β : Type} {input' : β ↪ List Bool} (hC : CtxPT input C) {g : β → α}
    (hg : ComputableInPolyTime g input' input) : CtxPT input' (fun b ↦ C (g b)) :=
  ⟨hC.n.comp hg, hC.m.comp hg, hC.tab.comp hg, hC.δ.comp hg, hC.ε.comp hg, hC.K.comp hg,
    hC.R.comp hg, hC.Pu.comp hg, hC.L.comp hg⟩

/-! ### Distances, offsets and profiles -/

theorem distG {j i : α → ℕ} (hC : CtxPT input C) (hj : ComputableInPolyTime j input encNat)
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).dist (j a) (i a)) input encRat :=
  listGetD_binary (encA := encRat) 0 (listGetD_binary (encA := encList encRat) [] hC.tab hj) hi

theorem offG {g : α → ℕ} (hC : CtxPT input C) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).off (g a)) input encRat :=
  rat_div' (rat_mul' hC.K (rat_natCast' hg)) (rat_two_pow' hC.Pu)

theorem aoffG {A : α → AAtom} (hC : CtxPT input C) (hA : ComputableInPolyTime A input encAt) :
    ComputableInPolyTime (fun a ↦ (C a).aoff (A a)) input encRat :=
  itep (decide_eq' ((snd _ _).comp hA) (const 0)) (const 0)
    (offG hC (binary_sub' ((snd _ _).comp hA) (const 1)))

theorem adistG {j : α → ℕ} {A : α → AAtom} (hC : CtxPT input C)
    (hj : ComputableInPolyTime j input encNat) (hA : ComputableInPolyTime A input encAt) :
    ComputableInPolyTime (fun a ↦ (C a).adist (j a) (A a)) input encRat :=
  rat_add' (distG hC hj ((fst _ _).comp hA)) (aoffG hC hA)

theorem profG {S : α → List AAtom} (hC : CtxPT input C)
    (hS : ComputableInPolyTime S input encSq) :
    ComputableInPolyTime (fun a ↦ (C a).prof (S a)) input (encList encRat) := by
  simp only [prof_eq]
  refine mapWithInput (f := fun a j ↦ ((S a).map ((C a).adist j)).foldl min (C a).ip.K)
    (unary_range' hC.n) (foldlMin ?_ (hC.comp (fst _ _)).K)
  exact mapWithInput (f := fun (p : α × ℕ) b ↦ (C p.1).adist p.2 b)
    (hS.comp (fst _ _)) (adistG (hC.comp ((fst _ _).comp (fst _ _)))
      (toBin ((snd _ _).comp (fst _ _))) (snd _ _))

/-! ### Times and sums -/

theorem θG {r : α → ℕ} (hC : CtxPT input C) (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a ↦ (C a).θ (r a)) input encRat :=
  ratPow (rat_add' (const 1) (rat_sq' hC.ε)) hr

theorem θseqG {p : α → ℕ} (hC : CtxPT input C) (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ (C a).θseq (p a)) input encRat :=
  θG hC (unDiv2 hp)

theorem θplusG {θ : α → ℚ} (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat) :
    ComputableInPolyTime (fun a ↦ (C a).θplus (θ a)) input encRat :=
  rat_mul' (rat_add' (const 1) (rat_sq' hC.ε)) hθ

theorem sumCG {g : α → ℕ → ℚ} (hC : CtxPT input C)
    (hg : ComputableInPolyTime (fun p : α × ℕ ↦ g p.1 p.2) (encPair input encUnary) encRat) :
    ComputableInPolyTime (fun a ↦ (C a).sumC (g a)) input encRat :=
  rat_sum' (mapWithInput (unary_range' hC.n) hg)

/-! ### The tests -/

theorem mvalG {θ : α → ℚ} {D : α → List ℚ} {j : α → ℕ} (hC : CtxPT input C)
    (hθ : ComputableInPolyTime θ input encRat) (hD : ComputableInPolyTime D input (encList encRat))
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).mval (θ a) (D a) (j a)) input encRat :=
  rat_min' hθ (rat_mul' (rat_sub' (const 1) hC.δ) (getDQ hD hj))

theorem lhs1G {θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).lhs1 (θ a) (D a) (i a)) input encRat :=
  sumCG hC (g := fun a j ↦ bid ((C a).mval (θ a) (D a) j)
      ((1 - (C a).ip.δ) * (C a).dist j (i a)))
    (bidQ (mvalG (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (rat_sub' (const 1) (hC.comp (fst _ _)).δ)
        (distG (hC.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))))

theorem gTG {θ e T : α → ℚ} (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (he : ComputableInPolyTime e input encRat) (hT : ComputableInPolyTime T input encRat) :
    ComputableInPolyTime (fun a ↦ (C a).gT (θ a) (e a) (T a)) input encRat :=
  itep (rat_le' he (rat_mul' hC.ε hθ))
    (rat_max' hθ (rat_min' hT (rat_sub' (rat_mul' (rat_add' (const 1) hC.ε) hθ) he))) hθ

theorem mTG {θ T : α → ℚ} {D : α → List ℚ} {i j : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).mT (θ a) (D a) (i a) (T a) (j a)) input encRat :=
  rat_min' (rat_mul' (rat_sub' (const 1) hC.δ) (getDQ hD hj))
    (gTG hC hθ (distG hC hj hi) hT)

theorem lhs3G {θ T : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) :
    ComputableInPolyTime (fun a ↦ (C a).lhs3 (θ a) (D a) (i a) (T a)) input encRat :=
  sumCG hC (g := fun a j ↦ bid ((C a).mT (θ a) (D a) (i a) (T a) j)
      ((1 - (C a).ip.δ / 2) * (C a).dist j (i a)))
    (bidQ (mTG (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
        (hT.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (rat_sub' (const 1) (rat_div' (hC.comp (fst _ _)).δ (const 2)))
        (distG (hC.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))))

theorem lhs4G {θ T : α → ℚ} {D : α → List ℚ} {i i₀ : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) (hi₀ : ComputableInPolyTime i₀ input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).lhs4 (θ a) (D a) (i a) (T a) (i₀ a)) input encRat :=
  sumCG hC (g := fun a j ↦ bid ((C a).mT (θ a) (D a) (i a) (T a) j) ((C a).dist j (i₀ a)))
    (bidQ (mTG (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
        (hT.comp (fst _ _)) (toBin (snd _ _)))
      (distG (hC.comp (fst _ _)) (toBin (snd _ _)) (hi₀.comp (fst _ _))))

theorem nearLG {θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).nearL (θ a) (D a) (i a)) input (encList encUnary) :=
  filterWithInput (test := fun a j ↦ decide ((C a).dist j (i a) ≤ (C a).ip.ε * θ a) &&
      decide (θ a < (1 - (C a).ip.δ) * (D a).getD j 0)) (unary_range' hC.n)
    (bool_and' (rat_le' (distG (hC.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))
        (rat_mul' (hC.comp (fst _ _)).ε (hθ.comp (fst _ _))))
      (rat_lt' (hθ.comp (fst _ _)) (rat_mul' (rat_sub' (const 1) (hC.comp (fst _ _)).δ)
        (getDQ (hD.comp (fst _ _)) (toBin (snd _ _))))))

theorem cnearG {θ : α → ℚ} {D : α → List ℚ} {i j : α → ℕ}
    (hC : CtxPT input C) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).cnear (θ a) (D a) (i a) (j a)) input encRat :=
  rat_min' (rat_mul' (rat_sub' (const 1) hC.δ) (getDQ hD hj))
    (rat_sub' (rat_mul' (rat_add' (const 1) hC.ε) hθ) (distG hC hj hi))

theorem needG {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).need (f a) (θ a) (D a) (i a)) input encRat := by
  unfold Ctx.need
  simp only [contains_eq]
  have hC' := hC.comp (fst input encUnary)
  have hN := nearLG hC hθ hD hi
  have hN' := nearLG hC' (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst input encUnary))
  refine rat_add' (rat_sub' hf (rat_sum' (mapWithInput (encA := encUnary) ?_ ?_)))
    (rat_sum' (mapWithInput hN ?_))
  · exact filterWithInput (test := fun a j ↦ !decide (j ∈ (C a).nearL (θ a) (D a) (i a)))
      (unary_range' hC.n) (bool_not.comp (decide_mem hN' (snd _ _)))
  · exact bidQ (mvalG hC' (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (rat_sub' (const 1) (rat_div' hC'.δ (const 2)))
        (distG hC' (toBin (snd _ _)) (hi.comp (fst _ _))))
  · exact rat_mul' (const γ) (rat_mul' (rat_sub' (const 1) (rat_div' hC'.δ (const 2)))
      (distG hC' (toBin (snd _ _)) (hi.comp (fst _ _))))

theorem candTG {f θ : α → ℚ} {D : α → List ℚ} {i j₀ : α → ℕ}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hj₀ : ComputableInPolyTime j₀ input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).candT (f a) (θ a) (D a) (i a) (j₀ a)) input encRat := by
  unfold Ctx.candT
  have hN := nearLG hC hθ hD hi
  have hc : ComputableInPolyTime (fun p : α × ℕ ↦ (C p.1).cnear (θ p.1) (D p.1) (i p.1) p.2)
      (encPair input encUnary) encRat :=
    cnearG (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
      (toBin (snd _ _))
  have hc₀ : ComputableInPolyTime (fun p : α × ℕ ↦ (C p.1).cnear (θ p.1) (D p.1) (i p.1)
      (j₀ p.1)) (encPair input encUnary) encRat :=
    cnearG (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
      (hj₀.comp (fst _ _))
  refine rat_div' (rat_sub' (needG hC hf hθ hD hi) (rat_sum' (mapWithInput
    (filterWithInput (test := fun a j ↦ decide ((C a).cnear (θ a) (D a) (i a) j <
      (C a).cnear (θ a) (D a) (i a) (j₀ a))) hN (rat_lt' hc hc₀)) hc)))
    (rat_natCast' (toBin ((length_list _).comp (filterWithInput (test := fun a j ↦
      decide ((C a).cnear (θ a) (D a) (i a) (j₀ a) ≤
        (C a).cnear (θ a) (D a) (i a) j)) hN (rat_le' hc₀ hc)))))

theorem tstarG {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).tstar (f a) (θ a) (D a) (i a)) input encRat :=
  foldlMax (mapWithInput (nearLG hC hθ hD hi)
    (candTG (hC.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _))
      (hi.comp (fst _ _)) (toBin (snd _ _)))) hθ

theorem test1G {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).test1 (f a) (θ a) (D a) (i a)) input encBool :=
  rat_le' hf (lhs1G hC hθ hD hi)

theorem test2G {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).test2 (f a) (θ a) (D a) (i a)) input encBool := by
  have hT := tstarG hC hf hθ hD hi
  have hT' := tstarG (hC.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
    (hD.comp (fst _ _)) (hi.comp (fst input encUnary))
  exact bool_and' (bool_and' (rat_le' hT (θplusG hC hθ)) (rat_le' hf (lhs3G hC hθ hD hi hT)))
    (allWithInput (test := fun a i₀ ↦ decide ((C a).lhs4 (θ a) (D a) (i a)
      ((C a).tstar (f a) (θ a) (D a) (i a)) i₀ ≤ f a)) (unary_range' hC.m)
      (rat_le' (lhs4G (hC.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _))
        (hi.comp (fst _ _)) hT' (toBin (snd _ _))) (hf.comp (fst _ _))))

theorem testTG {b : α → Bool} {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hC : CtxPT input C) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (C a).testT (b a) (f a) (θ a) (D a) (i a)) input encBool := by
  have h := ite' hb (test1G hC hf hθ hD hi) (test2G hC hf hθ hD hi)
  refine h.of_enc_eq fun a ↦ ?_
  unfold Ctx.testT
  cases b a <;> rfl

/-! ### CompleteSequence and CompleteSolution -/

theorem firstOpenG {b : α → Bool} {f θ : α → ℚ} {S : α → List AAtom}
    (hC : CtxPT input C) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hS : ComputableInPolyTime S input encSq) :
    ComputableInPolyTime (fun a ↦ (C a).firstOpen (b a) (f a) (θ a) (S a)) input
      (encOption encUnary) :=
  findWithInput (unary_range' hC.m)
    (testTG (hC.comp (fst _ _)) (hb.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
      (profG (hC.comp (fst _ _)) (hS.comp (fst _ _))) (toBin (snd _ _)))

theorem seqStepG {b : α → Bool} {f θ : α → ℚ} {pre cur : α → List AAtom}
    (hC : CtxPT input C) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hpre : ComputableInPolyTime pre input encSq) (hcur : ComputableInPolyTime cur input encSq) :
    ComputableInPolyTime (fun a ↦ (C a).seqStep (b a) (f a) (θ a) (pre a) (cur a)) input
      encSq := by
  simp only [seqStep_eq]
  exact optionElimWithInput (firstOpenG hC hb hf hθ (listAppend' hpre hcur)) hcur
    (listAppend' (hcur.comp (fst _ _)) (cons' ((toBin (snd _ _)).prod (const 0)) (const [])))

theorem completeSeqG {b : α → Bool} {f θ : α → ℚ} {pre cur : α → List AAtom}
    (hC : CtxPT input C) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hpre : ComputableInPolyTime pre input encSq) (hcur : ComputableInPolyTime cur input encSq) :
    ComputableInPolyTime (fun a ↦ (C a).completeSeq (b a) (f a) (θ a) (pre a) (cur a))
      input encSq := by
  unfold Ctx.completeSeq
  refine iterateWithInput_of_bounded_growth hC.L hcur
    (seqStepG (hC.comp (fst _ _)) (hb.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
      (hpre.comp (fst _ _)) (snd _ _))
    (growth := fun a ↦ 4 * (C a).ip.m + 3) ⟨?_, fun a s ↦ len_seqStep_le _ _ _ _ _ _⟩
  exact ((PolyBounded.const 4).mul hC.m.polyBounded).add (.const 3)

/-- **CompleteSolution runs in polynomial time** for a computed context. -/
theorem completeG {f : α → ℚ} {H : α → List (List AAtom)}
    (hC : CtxPT input C) (hf : ComputableInPolyTime f input encRat)
    (hH : ComputableInPolyTime H input encSl) :
    ComputableInPolyTime (fun a ↦ (C a).complete (f a) (H a)) input encSl := by
  unfold Ctx.complete
  have hC' : CtxPT (encPair (encPair input encSl) encUnary)
      (fun q : (α × List (List AAtom)) × ℕ ↦ C q.1.1) := hC.comp ((fst _ _).comp (fst _ _))
  have hH' : ComputableInPolyTime (fun q : (α × List (List AAtom)) × ℕ ↦ q.1.2)
      (encPair (encPair input encSl) encUnary) encSl := (snd _ _).comp (fst _ _)
  have hp : ComputableInPolyTime (fun q : (α × List (List AAtom)) × ℕ ↦ q.2)
      (encPair (encPair input encSl) encUnary) encUnary := snd _ _
  have hstep := itep (decide_eq' (lenL hH') hp)
    (listAppend' hH' (cons' (completeSeqG hC' (typ1B hp) (hf.comp ((fst _ _).comp (fst _ _)))
      (θseqG hC' hp) (flattenS hH') (const [])) (const []))) hH'
  refine foldlWithInput_of_bounded_growth hH
    ⟨unary_range' (unary_mul' (const 2) hC.R), hstep, inferInstance, inferInstance⟩
    (growth := fun a ↦ 2 * ((C a).ip.L * (2 * (2 * (C a).ip.m + 1) + 1)) + 1)
    ⟨?_, fun a s p _ ↦ len_complete_step _ _ _ _⟩
  exact ((PolyBounded.const 2).mul (hC.L.polyBounded.mul ((PolyBounded.const 2).mul
    (((PolyBounded.const 2).mul hC.m.polyBounded).add (.const 1)) |>.add (.const 1)))).add
    (.const 1)

end BCFGJPSSV26.FL.PT


