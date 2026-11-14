-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCtx
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxCtx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:25.767617+00:00
-- url     : https://prove2.me/theorems/8940b645-127a-4839-8a87-74dd7eade3ad
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxCtx — Polynomial time of the core: parameters, profiles and tests
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxCtx` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for the parameters of the core (`BCFGJPSSV26.Greedy.ipar`) and for the functions of
--   `BCFGJPSSV26.Greedy.Ctx` up to the tests, as functions of a core input `X a` (encoded by
--   `BCFGJPSSV26.Greedy.PT.encCI`) and of their other arguments. Every one of them is a fixed
--   composition of polynomial-time operations: maps, filters and sums over the `n` clients and the
--   `m` facilities, and folds of `min` and `max`.
--
--   **Contents.** The module is published as a whole: 45 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCtx`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxCtx.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxBasic

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxCtx` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: parameters, profiles and tests

Certificates for the parameters of the core (`BCFGJPSSV26.Greedy.ipar`) and for the functions of
`BCFGJPSSV26.Greedy.Ctx` up to the tests, as functions of a core input `X a` (encoded by
`BCFGJPSSV26.Greedy.PT.encCI`) and of their other arguments. Every one of them is a fixed
composition of polynomial-time operations: maps, filters and sums over the `n` clients and the
`m` facilities, and folds of `min` and `max`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool} (c : Consts) {X : α → CoreIn}

/-! ### The parameters -/

@[simp] theorem ctx_δ (x : CoreIn) : (ctx c x).ip.δ = c.δ := rfl
@[simp] theorem ctx_ε (x : CoreIn) : (ctx c x).ip.ε = c.εg := rfl
@[simp] theorem ctx_fmin (x : CoreIn) : (ctx c x).ip.fmin = c.δ := rfl

theorem nU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.n) input encUnary :=
  (fst _ _).comp hX

theorem mU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.m) input encUnary :=
  ((fst _ _).comp (snd _ _)).comp hX

theorem kB (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.k) input encNat :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp hX

theorem tabC (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).tab) input (encList (encList encRat)) :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp hX

theorem nQ (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ ((ctx c (X a)).ip.n : ℚ)) input encRat :=
  rat_natCast' (toBin (nU c hX))

theorem MQ (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.M) input encRat := by
  change ComputableInPolyTime (fun a ↦ 8 * ((ctx c (X a)).ip.n : ℚ) ^ 2 / c.εp + 1) input encRat
  exact rat_add' (rat_div' (rat_mul' (const 8) (rat_sq' (nQ c hX))) (const _)) (const 1)

theorem ηQ (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.η) input encRat := by
  change ComputableInPolyTime (fun a ↦ c.δ ^ 2 / (100 * ((ctx c (X a)).ip.n : ℚ) ^ 2)) input encRat
  exact rat_div' (const _) (rat_mul' (const 100) (rat_sq' (nQ c hX)))

theorem fmaxQ (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.fmax) input encRat := by
  change ComputableInPolyTime (fun a ↦ 4 * ((ctx c (X a)).ip.n : ℚ) * (ctx c (X a)).ip.M) input
    encRat
  exact rat_mul' (rat_mul' (const 4) (nQ c hX)) (MQ c hX)

theorem RU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.R) input encUnary := by
  change ComputableInPolyTime (fun a ↦ ⌈1 / c.εg ^ 2⌉₊ *
    Nat.clog 2 ⌈5 * ((ctx c (X a)).ip.n : ℚ) * (ctx c (X a)).ip.M⌉₊ + 1) input encUnary
  exact unary_add' (unary_mul' (const _) (clogU (natCeil (rat_mul' (rat_mul' (const 5)
    (nQ c hX)) (MQ c hX))))) (const 1)

theorem KQ (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.K) input encRat := by
  change ComputableInPolyTime (fun a ↦ 2 * (1 + c.εg ^ 2) ^ (ctx c (X a)).ip.R) input encRat
  exact rat_mul' (const 2) (ratPow (const _) (RU c hX))

theorem PfU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.Pf) input encUnary := by
  change ComputableInPolyTime (fun a ↦ Nat.clog 2 ⌈(ctx c (X a)).ip.fmax / (ctx c (X a)).ip.η⌉₊)
    input encUnary
  exact clogU (natCeil (rat_div' (fmaxQ c hX) (ηQ c hX)))

theorem PuU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.Pu) input encUnary := by
  change ComputableInPolyTime (fun a ↦ Nat.clog 2 ⌈(ctx c (X a)).ip.K / (ctx c (X a)).ip.η⌉₊)
    input encUnary
  exact clogU (natCeil (rat_div' (KQ c hX) (ηQ c hX)))

theorem LU (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).ip.L) input encUnary :=
  unary_add' (mU c hX) (const 4)

theorem twoPfB (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ 2 ^ (ctx c (X a)).ip.Pf) input encNat :=
  binary_two_pow.comp (PfU c hX)

theorem twoPuB (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ 2 ^ (ctx c (X a)).ip.Pu) input encNat :=
  binary_two_pow.comp (PuU c hX)

/-! ### Distances, offsets and profiles -/

theorem distQ {j i : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hj : ComputableInPolyTime j input encNat) (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).dist (j a) (i a)) input encRat :=
  listGetD_binary (encA := encRat) 0
    (listGetD_binary (encA := encList encRat) [] (tabC c hX) hj) hi

theorem offQ {g : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).off (g a)) input encRat :=
  rat_div' (rat_mul' (KQ c hX) (rat_natCast' hg)) (rat_two_pow' (PuU c hX))

theorem aoffQ {A : α → AAtom} (hX : ComputableInPolyTime X input encCI)
    (hA : ComputableInPolyTime A input encAt) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).aoff (A a)) input encRat :=
  itep (decide_eq' ((snd _ _).comp hA) (const 0)) (const 0)
    (offQ c hX (binary_sub' ((snd _ _).comp hA) (const 1)))

theorem adistQ {j : α → ℕ} {A : α → AAtom} (hX : ComputableInPolyTime X input encCI)
    (hj : ComputableInPolyTime j input encNat) (hA : ComputableInPolyTime A input encAt) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).adist (j a) (A a)) input encRat :=
  rat_add' (distQ c hX hj ((fst _ _).comp hA)) (aoffQ c hX hA)

theorem prof_eq (C : Ctx) (S : List AAtom) :
    C.prof S = (List.range C.ip.n).map fun j ↦ (S.map (C.adist j)).foldl min C.ip.K := by
  unfold Ctx.prof
  exact List.map_congr_left fun j _ ↦ foldr_min_eq _ _ _

theorem profL {S : α → List AAtom} (hX : ComputableInPolyTime X input encCI)
    (hS : ComputableInPolyTime S input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).prof (S a)) input (encList encRat) := by
  simp only [prof_eq]
  refine mapWithInput (f := fun a j ↦ ((S a).map ((ctx c (X a)).adist j)).foldl min
    (ctx c (X a)).ip.K) (unary_range' (nU c hX)) (foldlMin ?_ (KQ c (hX.comp (fst _ _))))
  exact mapWithInput (f := fun (p : α × ℕ) b ↦ (ctx c (X p.1)).adist p.2 b)
    (hS.comp (fst _ _)) (adistQ c (hX.comp ((fst _ _).comp (fst _ _)))
      (toBin ((snd _ _).comp (fst _ _))) (snd _ _))

/-! ### Times and sums -/

theorem θQ {r : α → ℕ} (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).θ (r a)) input encRat :=
  ratPow (const (1 + c.εg ^ 2)) hr

theorem θseqQ {p : α → ℕ} (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).θseq (p a)) input encRat :=
  θQ (X := X) c (unDiv2 hp)

theorem θplusQ {θ : α → ℚ} (hθ : ComputableInPolyTime θ input encRat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).θplus (θ a)) input encRat :=
  rat_mul' (const (1 + c.εg ^ 2)) hθ

theorem sumCQ {g : α → ℕ → ℚ} (hX : ComputableInPolyTime X input encCI)
    (hg : ComputableInPolyTime (fun p : α × ℕ ↦ g p.1 p.2) (encPair input encUnary) encRat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).sumC (g a)) input encRat :=
  rat_sum' (mapWithInput (unary_range' (nU c hX)) hg)

theorem bidQ {x y : α → ℚ} (hx : ComputableInPolyTime x input encRat)
    (hy : ComputableInPolyTime y input encRat) :
    ComputableInPolyTime (fun a ↦ bid (x a) (y a)) input encRat :=
  rat_max' (rat_sub' hx (rat_mul' (const γ) hy)) (const 0)

/-! ### The tests -/

theorem getDQ {D : α → List ℚ} {j : α → ℕ} (hD : ComputableInPolyTime D input (encList encRat))
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (D a).getD (j a) 0) input encRat :=
  listGetD_binary (encA := encRat) 0 hD hj

theorem mvalQ {θ : α → ℚ} {D : α → List ℚ} {j : α → ℕ}
    (hθ : ComputableInPolyTime θ input encRat) (hD : ComputableInPolyTime D input (encList encRat))
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).mval (θ a) (D a) (j a)) input encRat :=
  rat_min' hθ (rat_mul' (const (1 - c.δ)) (getDQ hD hj))

theorem lhs1Q {θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).lhs1 (θ a) (D a) (i a)) input encRat :=
  sumCQ c hX (g := fun a j ↦ bid ((ctx c (X a)).mval (θ a) (D a) j)
      ((1 - c.δ) * (ctx c (X a)).dist j (i a)))
    (bidQ (mvalQ c (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (const _) (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))))

theorem gTQ {θ e T : α → ℚ} (hθ : ComputableInPolyTime θ input encRat)
    (he : ComputableInPolyTime e input encRat) (hT : ComputableInPolyTime T input encRat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).gT (θ a) (e a) (T a)) input encRat :=
  itep (rat_le' he (rat_mul' (const c.εg) hθ))
    (rat_max' hθ (rat_min' hT (rat_sub' (rat_mul' (const (1 + c.εg)) hθ) he))) hθ

theorem mTQ {θ T : α → ℚ} {D : α → List ℚ} {i j : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).mT (θ a) (D a) (i a) (T a) (j a)) input
      encRat :=
  rat_min' (rat_mul' (const (1 - c.δ)) (getDQ hD hj))
    (gTQ (X := X) c hθ (distQ c hX hj hi) hT)

theorem lhs3Q {θ T : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).lhs3 (θ a) (D a) (i a) (T a)) input encRat :=
  sumCQ c hX (g := fun a j ↦ bid ((ctx c (X a)).mT (θ a) (D a) (i a) (T a) j)
      ((1 - c.δ / 2) * (ctx c (X a)).dist j (i a)))
    (bidQ (mTQ c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
        (hT.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (const _) (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))))

theorem lhs4Q {θ T : α → ℚ} {D : α → List ℚ} {i i₀ : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hT : ComputableInPolyTime T input encRat) (hi₀ : ComputableInPolyTime i₀ input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).lhs4 (θ a) (D a) (i a) (T a) (i₀ a)) input
      encRat :=
  sumCQ c hX (g := fun a j ↦ bid ((ctx c (X a)).mT (θ a) (D a) (i a) (T a) j)
      ((ctx c (X a)).dist j (i₀ a)))
    (bidQ (mTQ c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
        (hT.comp (fst _ _)) (toBin (snd _ _)))
      (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi₀.comp (fst _ _))))

theorem nearLL {θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).nearL (θ a) (D a) (i a)) input
      (encList encUnary) :=
  filterWithInput (test := fun a j ↦ decide ((ctx c (X a)).dist j (i a) ≤ c.εg * θ a) &&
      decide (θ a < (1 - c.δ) * (D a).getD j 0)) (unary_range' (nU c hX))
    (bool_and' (rat_le' (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _)))
        (rat_mul' (const _) (hθ.comp (fst _ _))))
      (rat_lt' (hθ.comp (fst _ _)) (rat_mul' (const _) (getDQ (hD.comp (fst _ _))
        (toBin (snd _ _))))))

theorem cnearQ {θ : α → ℚ} {D : α → List ℚ} {i j : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).cnear (θ a) (D a) (i a) (j a)) input encRat :=
  rat_min' (rat_mul' (const (1 - c.δ)) (getDQ hD hj))
    (rat_sub' (rat_mul' (const (1 + c.εg)) hθ) (distQ c hX hj hi))

theorem contains_eq (l : List ℕ) (j : ℕ) : l.contains j = decide (j ∈ l) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]

theorem needQ {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).need (f a) (θ a) (D a) (i a)) input encRat := by
  unfold Ctx.need
  simp only [contains_eq, ctx_δ]
  have hN := nearLL c hX hθ hD hi
  have hN' := nearLL c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _))
    (hi.comp (fst input encUnary))
  refine rat_add' (rat_sub' hf (rat_sum' (mapWithInput (encA := encUnary) ?_ ?_)))
    (rat_sum' (mapWithInput hN ?_))
  · exact filterWithInput (test := fun a j ↦ !decide (j ∈ (ctx c (X a)).nearL (θ a) (D a) (i a)))
      (unary_range' (nU c hX)) (bool_not.comp (decide_mem hN' (snd _ _)))
  · exact bidQ (mvalQ c (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (toBin (snd _ _)))
      (rat_mul' (const _) (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _))))
  · exact rat_mul' (const γ) (rat_mul' (const _)
      (distQ c (hX.comp (fst _ _)) (toBin (snd _ _)) (hi.comp (fst _ _))))

theorem candTQ {f θ : α → ℚ} {D : α → List ℚ} {i j₀ : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat)) (hi : ComputableInPolyTime i input encNat)
    (hj₀ : ComputableInPolyTime j₀ input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).candT (f a) (θ a) (D a) (i a) (j₀ a)) input
      encRat := by
  unfold Ctx.candT
  have hN := nearLL c hX hθ hD hi
  have hc : ComputableInPolyTime (fun p : α × ℕ ↦ (ctx c (X p.1)).cnear (θ p.1) (D p.1) (i p.1)
      p.2) (encPair input encUnary) encRat :=
    cnearQ c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
      (toBin (snd _ _))
  have hc₀ : ComputableInPolyTime (fun p : α × ℕ ↦ (ctx c (X p.1)).cnear (θ p.1) (D p.1) (i p.1)
      (j₀ p.1)) (encPair input encUnary) encRat :=
    cnearQ c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _)) (hi.comp (fst _ _))
      (hj₀.comp (fst _ _))
  refine rat_div' (rat_sub' (needQ c hX hf hθ hD hi) (rat_sum' (mapWithInput
    (filterWithInput (test := fun a j ↦ decide ((ctx c (X a)).cnear (θ a) (D a) (i a) j <
      (ctx c (X a)).cnear (θ a) (D a) (i a) (j₀ a))) hN (rat_lt' hc hc₀)) hc)))
    (rat_natCast' (toBin ((length_list _).comp (filterWithInput (test := fun a j ↦
      decide ((ctx c (X a)).cnear (θ a) (D a) (i a) (j₀ a) ≤
        (ctx c (X a)).cnear (θ a) (D a) (i a) j)) hN (rat_le' hc₀ hc)))))

theorem tstarQ {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).tstar (f a) (θ a) (D a) (i a)) input encRat :=
  foldlMax (mapWithInput (nearLL c hX hθ hD hi)
    (candTQ c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _))
      (hi.comp (fst _ _)) (toBin (snd _ _)))) hθ

theorem test1Q {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).test1 (f a) (θ a) (D a) (i a)) input encBool :=
  rat_le' hf (lhs1Q c hX hθ hD hi)

theorem test2Q {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).test2 (f a) (θ a) (D a) (i a)) input encBool := by
  have hT := tstarQ c hX hf hθ hD hi
  have hT' := tstarQ c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hθ.comp (fst _ _))
    (hD.comp (fst _ _)) (hi.comp (fst input encUnary))
  exact bool_and' (bool_and' (rat_le' hT (θplusQ c hθ)) (rat_le' hf (lhs3Q c hX hθ hD hi hT)))
    (allWithInput (test := fun a i₀ ↦ decide ((ctx c (X a)).lhs4 (θ a) (D a) (i a)
      ((ctx c (X a)).tstar (f a) (θ a) (D a) (i a)) i₀ ≤ f a)) (unary_range' (mU c hX))
      (rat_le' (lhs4Q c (hX.comp (fst _ _)) (hθ.comp (fst _ _)) (hD.comp (fst _ _))
        (hi.comp (fst _ _)) hT' (toBin (snd _ _))) (hf.comp (fst _ _))))

theorem testTQ {b : α → Bool} {f θ : α → ℚ} {D : α → List ℚ} {i : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hb : ComputableInPolyTime b input encBool)
    (hf : ComputableInPolyTime f input encRat) (hθ : ComputableInPolyTime θ input encRat)
    (hD : ComputableInPolyTime D input (encList encRat))
    (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).testT (b a) (f a) (θ a) (D a) (i a)) input
      encBool := by
  have h := ite' hb (test1Q c hX hf hθ hD hi) (test2Q c hX hf hθ hD hi)
  refine h.of_enc_eq fun a ↦ ?_
  unfold Ctx.testT
  cases b a <;> rfl

end BCFGJPSSV26.Greedy.PT


