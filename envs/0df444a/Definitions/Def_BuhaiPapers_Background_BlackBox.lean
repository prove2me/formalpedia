-- Prove2me | Definitions.Def_BuhaiPapers_Background_BlackBox
-- name    : BuhaiPapers_Background_BlackBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:10:39.277923+00:00
-- url     : https://prove2.me/theorems/bcd34bdc-b8f1-4ef7-b4e4-405141d45287
-- title:
--   Background.BlackBox — Algorithms that call other algorithms
-- statement:
--   This is module `Background.BlackBox`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   Tools for building a randomized algorithm from algorithms given only as machines, for instance by
--   the hypotheses of a theorem:
--
--   * **Black boxes in polynomial time.** A machine that runs within some bounds, not necessarily
--     polynomial in its input (`Turing.MultiTapeTM.ComputableInO`), applied to the values of a
--     polynomial-time map on which the bounds are polynomial, is polynomial-time
--     (`Turing.MultiTapeTM.ComputableInO.computableInPolyTime_comp`). Inside a polynomial-time
--     algorithm it can then be used like any other polynomial-time function, for instance mapped over
--     a list. A machine within time and space `t` is within `O(t)`
--     (`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInO`), and `2 ^ L` in unary is
--     polynomial-time when it is polynomially bounded
--     (`Turing.MultiTapeTM.ComputableInPolyTime.unary_two_pow`).
--   * **Reading a prefix of the coins.** An algorithm that reads only the first `N x` coins, for a
--     polynomial `N`, runs within `c ((|x| + 2)^D + |(x, r)| + 1)` steps and cells on an input `x`
--     with coins `r`, for any large `D`
--     (`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`): it keeps the first `N x` coins, in
--     time linear in the input plus a polynomial in `x`, and runs on the result.
--   * **Coins in blocks.** Among the strings of `o + T + q` coins, those whose block of `T` coins after
--     the first `o` satisfies a property are `2^(o + q)` times as many as the strings of `T` coins
--     satisfying it (`Encoding.natCard_window`). So an event that depends on one block of the coins
--     has the probability it has on that block alone.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_BlackBox`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/BlackBox.lean

module

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunPropLists
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_PolyTime
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.BlackBox` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Algorithms that call other algorithms

Tools for building a randomized algorithm from algorithms given only as machines, for instance by
the hypotheses of a theorem:

* **Black boxes in polynomial time.** A machine that runs within some bounds, not necessarily
  polynomial in its input (`Turing.MultiTapeTM.ComputableInO`), applied to the values of a
  polynomial-time map on which the bounds are polynomial, is polynomial-time
  (`Turing.MultiTapeTM.ComputableInO.computableInPolyTime_comp`). Inside a polynomial-time
  algorithm it can then be used like any other polynomial-time function, for instance mapped over
  a list. A machine within time and space `t` is within `O(t)`
  (`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInO`), and `2 ^ L` in unary is
  polynomial-time when it is polynomially bounded
  (`Turing.MultiTapeTM.ComputableInPolyTime.unary_two_pow`).
* **Reading a prefix of the coins.** An algorithm that reads only the first `N x` coins, for a
  polynomial `N`, runs within `c ((|x| + 2)^D + |(x, r)| + 1)` steps and cells on an input `x`
  with coins `r`, for any large `D`
  (`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`): it keeps the first `N x` coins, in
  time linear in the input plus a polynomial in `x`, and runs on the result.
* **Coins in blocks.** Among the strings of `o + T + q` coins, those whose block of `T` coins after
  the first `o` satisfies a property are `2^(o + q)` times as many as the strings of `T` coins
  satisfying it (`Encoding.natCard_window`). So an event that depends on one block of the coins
  has the probability it has on that block alone.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-! ### Black boxes in polynomial time -/

/-- A machine within time and space `t` computes its function within `O(t)`: its output is no
longer than its time. -/
theorem ComputableInTimeAndSpace.computableInO {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encMid t t) : ComputableInO f encIn encMid t t :=
  ⟨1, h.mono (fun _ ↦ by omega) (fun _ ↦ by omega), fun a ↦ (h.length_le a).trans (by omega)⟩

/-- **A black box on polynomial-time inputs.** If `f` is computable within bounds `T` and `S`, and
`g` in polynomial time, and both bounds are polynomial in the input on the values of `g`, then
`f ∘ g` is polynomial-time. -/
theorem ComputableInO.computableInPolyTime_comp {f : β → γ} {g : α → β} {T S : β → ℕ}
    (hf : ComputableInO f encMid encOut T S) (hg : ComputableInPolyTime g encIn encMid)
    (hT : PolyBounded (fun a ↦ (encIn a).length) fun a ↦ T (g a))
    (hS : PolyBounded (fun a ↦ (encIn a).length) fun a ↦ S (g a)) :
    ComputableInPolyTime (fun a ↦ f (g a)) encIn encOut := by
  obtain ⟨Tg, Sg, hTg, hSg, hg'⟩ := hg.exists_computableInO
  exact (hf.comp hg').computableInPolyTime (hTg.add hT) (hSg.add hS)

/-- **`2 ^ L` in unary**, for an exponent computable in unary, is polynomial-time when it is
polynomially bounded: double `L` times. -/
theorem ComputableInPolyTime.unary_two_pow {L : α → ℕ}
    (hL : ComputableInPolyTime L encIn encUnary)
    (hle : PolyBounded (fun a ↦ (encIn a).length) fun a ↦ 2 ^ L a) :
    ComputableInPolyTime (fun a ↦ 2 ^ L a) encIn encUnary := by
  obtain ⟨T, S, hT, hS, h⟩ := hL.exists_computableInO
  refine (ComputableInO.unary_two_pow.comp h).computableInPolyTime (hT.add ?_) (hS.add hle)
  exact (hle.mul hle).mono fun a ↦ Nat.mul_le_mul_right _ Nat.lt_two_pow_self

/-! ### Reading a prefix of the coins

The proof follows `BBKS24/RunTime.lean` and `BGHKLMM26/RunTime.lean`, which do the same for their
algorithms. -/

/-- A list of zeros and ones in unary is at most three times as long as the list. -/
theorem length_encList_unary_le {l : List ℕ} (h : ∀ c ∈ l, c ≤ 1) :
    (encList encUnary l).length ≤ 3 * l.length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc := h c List.mem_cons_self
    have := ih fun d hd ↦ h d (List.mem_cons_of_mem _ hd)
    simp only [List.map_cons, List.sum_cons, List.length_cons, encUnary_apply,
      List.length_replicate] at this ⊢
    omega

/-- A bit as a symbol is `0` or `1`. -/
theorem eBit_le_one (b : Bool) : Universal.eBit b ≤ 1 := by
  cases b <;> decide

/-- Bits turned into symbols and back. -/
theorem map_eBit_take (r : List Bool) (N : ℕ) :
    ((r.map Universal.eBit).take N).map (fun c ↦ decide (c = 1)) = r.take N := by
  rw [← List.map_take, List.map_map]
  conv_rhs => rw [← List.map_id (r.take N)]
  refine List.map_congr_left fun b _ ↦ ?_
  cases b <;> rfl

/-- The arithmetic of `Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`. -/
theorem take_bound_arith {A X L Y R E TLv TCv cL dL cC dC D K cM dM : ℕ}
    (hR : R ≤ A) (hE : E ≤ 3 * A) (hL : L ≤ cM * (X + 2) ^ dM) (hY : Y ≤ 2 * X + 1 + 3 * L)
    (hTL : TLv ≤ cL * (X + 1) ^ dL) (hTC : TCv ≤ cC * (Y + 1) ^ dC)
    (hD1 : dL ≤ D) (hD2 : (dM + 1) * dC ≤ D) (hD3 : dM + 1 ≤ D)
    (hK : 14 + cL + 3 * cM + cC * (3 * cM + 2) ^ dC ≤ K) :
    A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤ K * ((X + 2) ^ D + A + 1) := by
  obtain ⟨N, hN⟩ : ∃ N, N = X + 2 := ⟨_, rfl⟩
  rw [← hN] at hL ⊢
  have hN1 : 1 ≤ N := by omega
  have p1 : (X + 1) ^ dL ≤ N ^ D :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hN1 hD1)
  have p5 : N ^ (dM + 1) ≤ N ^ D := Nat.pow_le_pow_right hN1 hD3
  have hN5 : N ≤ N ^ (dM + 1) := Nat.le_self_pow (by omega) _
  have hL' : L ≤ cM * N ^ (dM + 1) :=
    hL.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 (Nat.le_succ _)))
  have hY1 : Y + 1 ≤ (3 * cM + 2) * N ^ (dM + 1) := by nlinarith
  have p2 : (Y + 1) ^ dC ≤ (3 * cM + 2) ^ dC * N ^ D :=
    calc (Y + 1) ^ dC ≤ ((3 * cM + 2) * N ^ (dM + 1)) ^ dC := Nat.pow_le_pow_left hY1 _
      _ = (3 * cM + 2) ^ dC * N ^ ((dM + 1) * dC) := by rw [mul_pow, ← pow_mul]
      _ ≤ (3 * cM + 2) ^ dC * N ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 hD2)
  obtain ⟨P, hP⟩ : ∃ P, P = N ^ D := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cC * (3 * cM + 2) ^ dC := ⟨_, rfl⟩
  rw [← hP] at p1 p2 p5
  have h1 : TLv ≤ cL * P := hTL.trans (Nat.mul_le_mul_left _ p1)
  have h2 : TCv ≤ Q * P := by
    rw [hQ, mul_assoc]
    exact hTC.trans (Nat.mul_le_mul_left _ p2)
  have h3 : L ≤ cM * P := hL'.trans (Nat.mul_le_mul_left _ p5)
  rw [← hP]
  have h4 : A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤
      (14 + cL + 3 * cM + Q) * (P + A + 1) := by
    have := Nat.zero_le (cL * A)
    have := Nat.zero_le (Q * A)
    have := Nat.zero_le (cM * A)
    have := Nat.zero_le cL
    have := Nat.zero_le Q
    have := Nat.zero_le cM
    nlinarith
  exact h4.trans (Nat.mul_le_mul_right _ (hQ ▸ hK))

/-- **An algorithm reading a polynomial prefix of its coins** runs within
`c ((|x| + 2)^E + |(x, r)| + 1)` steps and cells, for every large enough `E`: it turns the coins
into numbers and keeps the first `N x` of them, in time linear in the input plus a polynomial in
`x` (`Turing.MultiTapeTM.ComputableInO.take'`), then runs `A` on the result, in time polynomial
in `x`. -/
theorem exists_computableInTimeAndSpace_take {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : α × List Bool → β} {N : α → ℕ} {cN dN : ℕ}
    (hA : ComputableInPolyTime A (encPair encA encBits) encB)
    (hN : ComputableInPolyTime N encA encUnary)
    (hNle : ∀ a, N a ≤ cN * ((encA a).length + 2) ^ dN) :
    ∃ D, ∀ E, D ≤ E → ∃ c, ComputableInTimeAndSpace
      (fun x : α × List Bool ↦ A (x.1, x.2.take (N x.1))) (encPair encA encBits) encB
      (fun x ↦ c * (((encA x.1).length + 2) ^ E + (encPair encA encBits x).length + 1))
      (fun x ↦ c * (((encA x.1).length + 2) ^ E + (encPair encA encBits x).length + 1)) := by
  -- the algorithm on coins given as numbers
  set A' : α × List ℕ → β := fun y ↦ A (y.1, y.2.map fun c ↦ decide (c = 1)) with hA'def
  have hA' : ComputableInPolyTime A' (encPair encA (encList encUnary)) encB := by
    have hc : ComputableInPolyTime (fun y : α × List ℕ ↦ y.2.map fun c ↦ decide (c = 1))
        (encPair encA (encList encUnary)) (encList encBool) :=
      ComputableInPolyTime.mapWithInput (f := fun _ (c : ℕ) ↦ decide (c = 1)) (by fun_prop)
        (by fun_prop)
    have hb : ComputableInPolyTime (fun y : α × List ℕ ↦ y.2.map fun c ↦ decide (c = 1))
        (encPair encA (encList encUnary)) encBits :=
      .of_tidy (ComputableTidilyInPolyTime.listToBits.comp hc.tidy)
    exact hA.comp ((ComputableInPolyTime.fst _ _).prod hb)
  obtain ⟨TL, SL, hTL, hSL, hL⟩ := hN.exists_computableInO
  obtain ⟨TC, SC, hTC, hSC, hC⟩ := hA'.exists_computableInO
  obtain ⟨cTL, dTL, hTL'⟩ := hTL.exists_le
  obtain ⟨cSL, dSL, hSL'⟩ := hSL.exists_le
  obtain ⟨cTC, dTC, hTC'⟩ := hTC.exists_le
  obtain ⟨cSC, dSC, hSC'⟩ := hSC.exists_le
  have hfst := ComputableInO.fst encA encBits
  have hsnd := ComputableInO.snd encA encBits
  have hmap := (Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO).comp' hsnd
  have hlen := hL.comp' hfst
  have htake := ComputableInO.take' hmap hlen
  have htr := ComputableInO.prod hfst htake
  have hall := hC.comp' htr
  have halg : (fun x : α × List Bool ↦
      A' (x.1, List.take (N x.1) (List.map (⇑Universal.eBit) x.2))) =
      fun x ↦ A (x.1, x.2.take (N x.1)) :=
    funext fun x ↦ by simp only [hA'def, map_eBit_take]
  rw [halg] at hall
  refine ⟨dTL + dSL + (dN + 1) * (dTC + dSC) + dN + 1, fun E hE ↦ ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 14 + (cTL + cSL) + 3 * cN + (cTC + cSC) * (3 * cN + 2) ^ (dTC + dSC) :=
    ⟨_, rfl⟩
  have hK1 : 14 + cTL + 3 * cN + cTC * (3 * cN + 2) ^ dTC ≤ K := by
    have : cTC * (3 * cN + 2) ^ dTC ≤ (cTC + cSC) * (3 * cN + 2) ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hK2 : 14 + cSL + 3 * cN + cSC * (3 * cN + 2) ^ dSC ≤ K := by
    have : cSC * (3 * cN + 2) ^ dSC ≤ (cTC + cSC) * (3 * cN + 2) ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hD2 : (dN + 1) * dTC ≤ E :=
    (Nat.mul_le_mul_left _ (Nat.le_add_right dTC dSC)).trans (by omega)
  have hD2' : (dN + 1) * dSC ≤ E :=
    (Nat.mul_le_mul_left _ (Nat.le_add_left dSC dTC)).trans (by omega)
  -- the lengths
  have hlens : ∀ x : α × List Bool,
      (encBits x.2).length ≤ (encPair encA encBits x).length ∧
      (encList encUnary (List.map (⇑Universal.eBit) x.2)).length ≤
        3 * (encPair encA encBits x).length ∧
      (encPair (encList encUnary) encUnary
          (List.map (⇑Universal.eBit) x.2, N x.1)).length =
        2 * (encList encUnary (List.map (⇑Universal.eBit) x.2)).length + 1 + N x.1 ∧
      (encPair encA (encList encUnary)
          (x.1, List.take (N x.1) (List.map (⇑Universal.eBit) x.2))).length ≤
        2 * (encA x.1).length + 1 + 3 * N x.1 := by
    intro x
    have hA := length_encPair (enc₁ := encA) (enc₂ := encBits) x
    have hm : (encList encUnary (List.map (⇑Universal.eBit) x.2)).length ≤
        3 * (List.map (⇑Universal.eBit) x.2).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
        exact eBit_le_one b
    have ht : (encList encUnary (List.take (N x.1) (List.map (⇑Universal.eBit) x.2))).length
        ≤ 3 * (List.take (N x.1) (List.map (⇑Universal.eBit) x.2)).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hc)
        exact eBit_le_one b
    have hlt := List.length_take_le (N x.1) (List.map (⇑Universal.eBit) x.2)
    rw [List.length_map] at hm
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have : x.2.length = (encBits x.2).length := rfl
      omega
    · rw [length_encPair, encUnary_apply, List.length_replicate]
    · simp only [length_encPair]
      omega
  obtain ⟨c, hc, -⟩ := hall.mono (T' := fun x ↦ ((encA x.1).length + 2) ^ E +
      (encPair encA encBits x).length)
    (S' := fun x ↦ ((encA x.1).length + 2) ^ E + (encPair encA encBits x).length) K
    (fun x ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens x
      rw [h3]
      exact take_bound_arith h1 h2 (hNle x.1) h4 (hTL' x.1) (hTC' _) (by omega) hD2
        (by omega) hK1)
    (fun x ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens x
      rw [h3]
      exact take_bound_arith h1 h2 (hNle x.1) h4 (hSL' x.1) (hSC' _) (by omega) hD2'
        (by omega) hK2)
  exact ⟨c, hc⟩

end Turing.MultiTapeTM

namespace Encoding

/-! ### Coins in blocks -/

/-- The equivalence between strings of `o + T + q` coins and their three blocks. -/
def blocksEquiv (o T q : ℕ) :
    ((Fin o → Bool) × (Fin T → Bool)) × (Fin q → Bool) ≃ (Fin (o + T + q) → Bool) :=
  (Equiv.prodCongr (Fin.appendEquiv o T) (Equiv.refl _)).trans (Fin.appendEquiv (o + T) q)

theorem window_blocksEquiv (o T q : ℕ) (t : ((Fin o → Bool) × (Fin T → Bool)) × (Fin q → Bool)) :
    ((List.ofFn (blocksEquiv o T q t)).drop o).take T = List.ofFn t.1.2 := by
  change ((List.ofFn (Fin.append (Fin.append t.1.1 t.1.2) t.2)).drop o).take T = _
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.append_assoc,
    List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn]

/-- **Coins in blocks.** Among the strings of `o + T + q` coins, those whose block of `T` coins
after the first `o` satisfies `P` are `2^(o + q)` times as many as the strings of `T` coins
satisfying `P`. -/
theorem natCard_window (P : List Bool → Prop) (o T q : ℕ) :
    Nat.card {r : Fin (o + T + q) → Bool // P (((List.ofFn r).drop o).take T)} =
      2 ^ (o + q) * Nat.card {w : Fin T → Bool // P (List.ofFn w)} := by
  have e₁ : {r : Fin (o + T + q) → Bool // P (((List.ofFn r).drop o).take T)} ≃
      {t : ((Fin o → Bool) × (Fin T → Bool)) × (Fin q → Bool) // P (List.ofFn t.1.2)} :=
    ((blocksEquiv o T q).subtypeEquiv fun t ↦ by rw [window_blocksEquiv]).symm
  have e₂ : {t : ((Fin o → Bool) × (Fin T → Bool)) × (Fin q → Bool) // P (List.ofFn t.1.2)} ≃
      ((Fin o → Bool) × {w : Fin T → Bool // P (List.ofFn w)}) × (Fin q → Bool) :=
    { toFun t := ((t.1.1.1, ⟨t.1.1.2, t.2⟩), t.1.2)
      invFun s := ⟨((s.1.1, s.1.2.1), s.2), s.1.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  ring

end Encoding


