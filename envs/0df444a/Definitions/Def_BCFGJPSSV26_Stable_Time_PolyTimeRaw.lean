-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeRaw
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeRaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:16:15.03291+00:00
-- url     : https://prove2.me/theorems/5a46b97c-a072-4458-af14-73ae402ad665
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeRaw — Exact distances and costs in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeRaw` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for the exact computations of `BCFGJPSSV26/Basic/Raw.lean` and
--   `BCFGJPSSV26/Stable/Alg/Mixed.lean` on tuples `x : Raw`, in the compositional form of
--   complexitylib (`fun a ↦ g (f a)` from certificates for `f`): table lookups, distances to lists of
--   facilities and dummies, nearest facilities, clusters, costs and balls.
--
--   Numbers of clients and facilities are written in binary in a tuple, so enumerating them is
--   polynomial-time only when they are at most the number of rows of the table, as for an instance;
--   the enumerations take this as a hypothesis (`BCFGJPSSV26.Stable.PolyTime.rangeN'`).
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeRaw`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeRaw.lean

module

public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeRaw` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Exact distances and costs in polynomial time

Certificates for the exact computations of `BCFGJPSSV26/Basic/Raw.lean` and
`BCFGJPSSV26/Stable/Alg/Mixed.lean` on tuples `x : Raw`, in the compositional form of
complexitylib (`fun a ↦ g (f a)` from certificates for `f`): table lookups, distances to lists of
facilities and dummies, nearest facilities, clusters, costs and balls.

Numbers of clients and facilities are written in binary in a tuple, so enumerating them is
polynomial-time only when they are at most the number of rows of the table, as for an instance;
the enumerations take this as a hypothesis (`BCFGJPSSV26.Stable.PolyTime.rangeN'`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable.PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The tuple -/

@[fun_prop]
theorem raw_n' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).n) input encNat := (fst _ _).comp hf

@[fun_prop]
theorem raw_m' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).m) input encNat := ((fst _ _).comp (snd _ _)).comp hf

@[fun_prop]
theorem raw_k' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).k) input encNat :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp hf

@[fun_prop]
theorem raw_table' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).table) input (encList (encList encRat)) :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp hf

/-- The number of rows of the table, in unary. -/
theorem raw_rows' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).table.length) input encUnary :=
  (length_list _).comp (raw_table' hf)

/-- A number at most the number of rows of the table, in unary. -/
theorem le_rows_unary {f : α → Raw} {v : α → ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hv : ComputableInPolyTime v input encNat) (hle : ∀ a, v a ≤ (f a).table.length) :
    ComputableInPolyTime v input encUnary :=
  binary_to_unary_bounded hv (raw_rows' hf) hle

/-- The numbers below one at most the number of rows of the table, in binary. -/
theorem rangeN' {f : α → Raw} {v : α → ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hv : ComputableInPolyTime v input encNat) (hle : ∀ a, v a ≤ (f a).table.length) :
    ComputableInPolyTime (fun a ↦ List.range (v a)) input (encList encNat) := by
  have h : ComputableInPolyTime (fun a ↦ (List.range (v a)).map fun i ↦ i) input
      (encList encNat) :=
    mapWithInput (unary_range' (le_rows_unary hf hv hle)) (unary_to_binary.comp (snd _ _))
  simpa only [List.map_id'] using h

/-! ### Distances -/

/-- Addition of binary numbers. -/
theorem binAdd' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hf.tidy hg.tidy)

/-- Multiplication of binary numbers. -/
theorem binMul' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a * g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mul' hf.tidy hg.tidy)

@[fun_prop]
theorem dist' {f : α → Raw} {p q : α → ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hp : ComputableInPolyTime p input encNat) (hq : ComputableInPolyTime q input encNat) :
    ComputableInPolyTime (fun a ↦ (f a).dist (p a) (q a)) input encRat := by
  unfold Raw.dist
  exact listGetD_binary (encA := encRat) 0
    (listGetD_binary (encA := encList encRat) [] (raw_table' hf) hp) hq

@[fun_prop]
theorem fdist' {f : α → Raw} {p i : α → ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hp : ComputableInPolyTime p input encNat) (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (f a).fdist (p a) (i a)) input encRat := by
  unfold Raw.fdist
  exact dist' hf hp (binAdd' (raw_n' hf) hi)

@[fun_prop]
theorem dMaxQ' {f : α → Raw} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ (f a).dMaxQ) input encRat := by
  unfold Raw.dMaxQ
  have h : ComputableInPolyTime (fun a ↦ (f a).table.map List.sum) input (encList encRat) :=
    mapWithInput (f := fun _ (r : List ℚ) ↦ r.sum) (raw_table' hf) (rat_sum' (snd _ _))
  exact rat_add' (const 1) (rat_sum' h)

@[fun_prop]
theorem dSetQ' {f : α → Raw} {p : α → ℕ} {S : α → List ℕ}
    (hf : ComputableInPolyTime f input encRaw) (hp : ComputableInPolyTime p input encNat)
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).dSetQ (p a) (S a)) input encRat := by
  unfold Raw.dSetQ
  have hmap : ComputableInPolyTime (fun a ↦ (S a).map ((f a).fdist (p a))) input
      (encList encRat) :=
    mapWithInput (f := fun a i ↦ (f a).fdist (p a) i) hS
      (fdist' (hf.comp (fst _ _)) (hp.comp (fst _ _)) (snd _ _))
  have hc : ComputableInPolyTime (fun a ↦ decide (S a = [])) input encBool :=
    ((listIsEmpty (encA := encNat)).comp hS).of_enc_eq fun a ↦ by
      change encBool (decide (S a = [])) = encBool (S a).isEmpty
      cases S a <;> rfl
  exact ite_decide hc (dMaxQ' hf) (Combine.minQ_polytime hmap)

@[fun_prop]
theorem cost' {f : α → Raw} {S : α → List ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).cost (S a)) input encRat := by
  unfold Raw.cost
  exact Combine.costQ_polytime (raw_n' hf) (raw_table' hf) hS

@[fun_prop]
theorem costOn' {f : α → Raw} {S D : α → List ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hS : ComputableInPolyTime S input (encList encNat))
    (hD : ComputableInPolyTime D input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).costOn (S a) (D a)) input encRat := by
  unfold Raw.costOn
  exact rat_sum' (mapWithInput (f := fun a j ↦ (f a).dSetQ j (S a)) hD
    (dSetQ' (hf.comp (fst _ _)) (snd _ _) (hS.comp (fst _ _))))

/-! ### Nearest facilities and clusters -/

@[fun_prop]
theorem nearLE' {f : α → Raw} {p i i' : α → ℕ} (hf : ComputableInPolyTime f input encRaw)
    (hp : ComputableInPolyTime p input encNat) (hi : ComputableInPolyTime i input encNat)
    (hi' : ComputableInPolyTime i' input encNat) :
    ComputableInPolyTime (fun a ↦ (f a).nearLE (p a) (i a) (i' a)) input encBool := by
  unfold Raw.nearLE
  have h1 := rat_lt' (fdist' hf hp hi) (fdist' hf hp hi')
  have h2 := decide_eq' (fdist' hf hp hi) (fdist' hf hp hi')
  have h4 := binary_le' hi hi'
  have h : ComputableInPolyTime (fun a ↦ decide ((f a).fdist (p a) (i a) < (f a).fdist (p a)
      (i' a)) || (decide ((f a).fdist (p a) (i a) = (f a).fdist (p a) (i' a)) &&
        decide (i a ≤ i' a))) input encBool := bool_or.comp (h1.prod (bool_and' h2 h4))
  refine h.of_enc_eq fun a ↦ ?_
  rw [Bool.decide_or, Bool.decide_and]

@[fun_prop]
theorem nearQ' {f : α → Raw} {p : α → ℕ} {S : α → List ℕ}
    (hf : ComputableInPolyTime f input encRaw) (hp : ComputableInPolyTime p input encNat)
    (hS : ComputableInPolyTime S input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).nearQ (p a) (S a)) input encNat := by
  unfold Raw.nearQ
  have hall : ComputableInPolyTime (fun q : α × ℕ ↦ (S q.1).all fun i' ↦
      (f q.1).nearLE (p q.1) q.2 i') (encPair input encNat) encBool :=
    allWithInput (test := fun (q : α × ℕ) i' ↦ (f q.1).nearLE (p q.1) q.2 i') (hS.comp (fst _ _))
      (nearLE' (hf.comp ((fst _ _).comp (fst _ _))) (hp.comp ((fst _ _).comp (fst _ _)))
        ((snd _ _).comp (fst _ _)) (snd _ _))
  exact (optionGetD encNat).comp ((findWithInput
    (test := fun a i ↦ (S a).all fun i' ↦ (f a).nearLE (p a) i i') hS hall).prod (const 0))

/-- Equality of binary numbers. -/
theorem decide_eq_nat {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ decide (f a = g a)) input encBool :=
  decide_eq' hf hg

/-- The clusters, when the clients are at most the rows of the table. -/
theorem clusterQ' {f : α → Raw} {S : α → List ℕ} {c : α → ℕ}
    (hf : ComputableInPolyTime f input encRaw) (hn : ∀ a, (f a).n ≤ (f a).table.length)
    (hS : ComputableInPolyTime S input (encList encNat))
    (hc : ComputableInPolyTime c input encNat) :
    ComputableInPolyTime (fun a ↦ (f a).clusterQ (S a) (c a)) input (encList encNat) := by
  unfold Raw.clusterQ
  exact filterWithInput (test := fun a j ↦ decide ((f a).nearQ j (S a) = c a))
    (rangeN' hf (raw_n' hf) hn)
    (decide_eq_nat (nearQ' (hf.comp (fst _ _)) (snd _ _) (hS.comp (fst _ _)))
      (hc.comp (fst _ _)))

/-! ### Dummies and mixed sets -/

/-- The encoding of exact dummies. -/
abbrev encDum : DumQ ↪ List Bool := encPair encNat encRat

/-- The nearest of a list of values and a default, as a fold. -/
theorem foldr_min_eq_minQ {β : Type} (g : β → ℚ) (d : ℚ) (l : List β) :
    l.foldr (fun b acc ↦ min (g b) acc) d = Combine.minQ (l.map g ++ [d]) := by
  have hne : l.map g ++ [d] ≠ [] := by simp
  obtain ⟨hmem, hle⟩ := Combine.minQ_spec hne
  have hfold : ∀ l : List β, l.foldr (fun b acc ↦ min (g b) acc) d ∈ l.map g ++ [d] ∧
      ∀ q ∈ l.map g ++ [d], l.foldr (fun b acc ↦ min (g b) acc) d ≤ q := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      obtain ⟨h1, h2⟩ := ih
      set v := l.foldr (fun b acc ↦ min (g b) acc) d with hv
      rw [List.foldr_cons, ← hv, List.map_cons, List.cons_append]
      refine ⟨?_, ?_⟩
      · rcases min_choice (g b) v with h | h
        · rw [h]
          exact List.mem_cons_self
        · rw [h]
          exact List.mem_cons_of_mem _ h1
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (h2 q hq)
  obtain ⟨h1, h2⟩ := hfold l
  exact le_antisymm (h2 _ hmem) (hle _ h1)

@[fun_prop]
theorem dDumsQ' {f : α → Raw} {p : α → ℕ} {Λ : α → List DumQ}
    (hf : ComputableInPolyTime f input encRaw) (hp : ComputableInPolyTime p input encNat)
    (hΛ : ComputableInPolyTime Λ input (encList encDum)) :
    ComputableInPolyTime (fun a ↦ (f a).dDumsQ (p a) (Λ a)) input encRat := by
  have heq : ∀ a, (f a).dDumsQ (p a) (Λ a) =
      Combine.minQ ((Λ a).map (fun l ↦ (f a).dist (p a) l.1 + l.2) ++ [(f a).dMaxQ]) :=
    fun a ↦ foldr_min_eq_minQ _ _ _
  simp only [heq]
  have hmap : ComputableInPolyTime (fun a ↦ (Λ a).map fun l ↦ (f a).dist (p a) l.1 + l.2)
      input (encList encRat) :=
    mapWithInput (f := fun a (l : DumQ) ↦ (f a).dist (p a) l.1 + l.2) hΛ
      (rat_add' (dist' (hf.comp (fst _ _)) (hp.comp (fst _ _)) ((fst _ _).comp (snd _ _)))
        ((snd _ _).comp (snd _ _)))
  exact Combine.minQ_polytime (listAppend' hmap (cons' (dMaxQ' hf) (const [])))

@[fun_prop]
theorem dMixQ' {f : α → Raw} {p : α → ℕ} {F : α → List ℕ} {Λ : α → List DumQ}
    (hf : ComputableInPolyTime f input encRaw) (hp : ComputableInPolyTime p input encNat)
    (hF : ComputableInPolyTime F input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum)) :
    ComputableInPolyTime (fun a ↦ (f a).dMixQ (p a) (F a) (Λ a)) input encRat := by
  unfold Raw.dMixQ
  exact rat_min' (dSetQ' hf hp hF) (dDumsQ' hf hp hΛ)

theorem clusterMixQ' {f : α → Raw} {F : α → List ℕ} {Λ : α → List DumQ} {c : α → ℕ}
    (hf : ComputableInPolyTime f input encRaw) (hn : ∀ a, (f a).n ≤ (f a).table.length)
    (hF : ComputableInPolyTime F input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hc : ComputableInPolyTime c input encNat) :
    ComputableInPolyTime (fun a ↦ (f a).clusterMixQ (F a) (Λ a) (c a)) input
      (encList encNat) := by
  unfold Raw.clusterMixQ
  have hf' : ComputableInPolyTime (fun q : α × ℕ ↦ f q.1) (encPair input encNat) encRaw :=
    hf.comp (fst _ _)
  exact filterWithInput (test := fun a j ↦ decide ((f a).nearQ j (F a) = c a) &&
      decide ((f a).dSetQ j (F a) ≤ (f a).dDumsQ j (Λ a)))
    (rangeN' hf (raw_n' hf) hn)
    (bool_and' (decide_eq_nat (nearQ' hf' (snd _ _) (hF.comp (fst _ _))) (hc.comp (fst _ _)))
      (rat_le' (dSetQ' hf' (snd _ _) (hF.comp (fst _ _)))
        (dDumsQ' hf' (snd _ _) (hΛ.comp (fst _ _)))))

@[fun_prop]
theorem costMixOnQ' {f : α → Raw} {F D : α → List ℕ} {Λ : α → List DumQ}
    (hf : ComputableInPolyTime f input encRaw)
    (hF : ComputableInPolyTime F input (encList encNat))
    (hΛ : ComputableInPolyTime Λ input (encList encDum))
    (hD : ComputableInPolyTime D input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).costMixOnQ (F a) (Λ a) (D a)) input encRat := by
  unfold Raw.costMixOnQ
  exact rat_sum' (mapWithInput (f := fun a j ↦ (f a).dMixQ j (F a) (Λ a)) hD
    (dMixQ' (hf.comp (fst _ _)) (snd _ _) (hF.comp (fst _ _)) (hΛ.comp (fst _ _))))

/-- The balls, when the facilities are at most the rows of the table. -/
theorem ballQ' {f : α → Raw} {l : α → DumQ} (hf : ComputableInPolyTime f input encRaw)
    (hm : ∀ a, (f a).m ≤ (f a).table.length) (hl : ComputableInPolyTime l input encDum) :
    ComputableInPolyTime (fun a ↦ (f a).ballQ (l a)) input (encList encNat) := by
  unfold Raw.ballQ
  exact filterWithInput (test := fun a i ↦ decide ((f a).fdist (l a).1 i ≤ (l a).2))
    (rangeN' hf (raw_m' hf) hm)
    (rat_le' (fdist' (hf.comp (fst _ _)) ((fst _ _).comp (hl.comp (fst _ _))) (snd _ _))
      ((snd _ _).comp (hl.comp (fst _ _))))

end BCFGJPSSV26.Stable.PolyTime


