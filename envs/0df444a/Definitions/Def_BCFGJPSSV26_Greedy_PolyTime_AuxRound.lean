-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxRound
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxRound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:11:48.584798+00:00
-- url     : https://prove2.me/theorems/706132da-74e4-4727-81f7-f567c7887f5f
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxRound — Polynomial time of the core: certificates of the walk
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxRound` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   `BCFGJPSSV26.Greedy.PT.roundBS` (a round of the walk: an iteration of deletions, with the bounds
--   of `BCFGJPSSV26.Greedy.PT.iterate_delStep_inv`) and `BCFGJPSSV26.Greedy.PT.walkBS` (`L` rounds,
--   with the bounds of `BCFGJPSSV26.Greedy.PT.walkB_inv`).
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxRound`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxRound.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxWalk

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxRound` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: certificates of the walk

`BCFGJPSSV26.Greedy.PT.roundBS` (a round of the walk: an iteration of deletions, with the bounds
of `BCFGJPSSV26.Greedy.PT.iterate_delStep_inv`) and `BCFGJPSSV26.Greedy.PT.walkBS` (`L` rounds,
with the bounds of `BCFGJPSSV26.Greedy.PT.walkB_inv`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- The state of a round after its deletions. -/
def rdel (C : Ctx) (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Hp : List AAtom)
    (st : List AAtom × List (List AAtom × Ctx.WKind)) :
    List AAtom × List (List AAtom × Ctx.WKind) :=
  (C.delStep p f pre (Ctx.commonPrefixLen Hp st.1))^[st.1.length - Ctx.commonPrefixLen Hp st.1]
    (st.1 ++ [((Hp.getD (Ctx.commonPrefixLen Hp st.1) (0, 0)).1, 1)],
      st.2 ++ [(st.1 ++ [((Hp.getD (Ctx.commonPrefixLen Hp st.1) (0, 0)).1, 1)],
        .appendFree (Hp.getD (Ctx.commonPrefixLen Hp st.1) (0, 0)).1)])

theorem roundB_eq (C : Ctx) (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (Hp : List AAtom)
    (st : List AAtom × List (List AAtom × Ctx.WKind)) :
    C.roundB p f pre Hp st = if Hp.isPrefixOf st.1 then st else
      ((rdel C p f pre Hp st).1.set (Ctx.commonPrefixLen Hp st.1)
          ((Hp.getD (Ctx.commonPrefixLen Hp st.1) (0, 0)).1, 0),
        (rdel C p f pre Hp st).2 ++ [((rdel C p f pre Hp st).1.set (Ctx.commonPrefixLen Hp st.1)
          ((Hp.getD (Ctx.commonPrefixLen Hp st.1) (0, 0)).1, 0), .toRegular)]) := by
  unfold Ctx.roundB rdel
  split_ifs <;> rfl

theorem len_encWS_le {s : List AAtom × List (List AAtom × Ctx.WKind)}
    {l₀ new : List (List AAtom × Ctx.WKind)} {e₀ : List AAtom × Ctx.WKind} {A E i cnt : ℕ}
    (h1 : (encSq s.1).length ≤ A) (h2 : s.2 = (l₀ ++ [e₀]) ++ new) (he₀ : (encPt e₀).length ≤ E)
    (hnew : (encList encPt new).length ≤ i * (2 * E + 1)) (hi : i ≤ cnt) :
    (encWS s).length ≤ 2 * A + 1 + (encList encPt l₀).length + (cnt + 1) * (2 * E + 1) := by
  rw [show (encWS s).length = 2 * (encSq s.1).length + 1 + (encList encPt s.2).length from
    length_encPair s, h2, len_encList_append, len_encList_append]
  simp only [encList_cons, encList_nil, List.append_nil, length_frame]
  have := Nat.mul_le_mul_right (2 * E + 1) hi
  rw [add_one_mul]
  omega

theorem len_encWS_le' {s : List AAtom × List (List AAtom × Ctx.WKind)} {σ N K ℓ : ℕ}
    (h1 : PSeq (fun a ↦ (encAt a).length ≤ σ) ℓ s.1) (hℓ : ℓ ≤ N) (h2 : s.2.length ≤ K)
    (h3 : ∀ e ∈ s.2, PEnt (fun a ↦ (encAt a).length ≤ σ) N e) :
    (encWS s).length ≤ 2 * (N * (2 * σ + 1)) + 1 + K * (2 * entB σ N + 1) := by
  rw [show (encWS s).length = 2 * (encSq s.1).length + 1 + (encList encPt s.2).length from
    length_encPair s]
  have := len_PSeq (h1.mono hℓ)
  have := len_ents h2 h3
  omega

variable {α : Type} {input : α ↪ List Bool}

theorem PolyBounded.entB' {σ N : α → ℕ} (hσ : PolyBounded (fun a ↦ (input a).length) σ)
    (hN : PolyBounded (fun a ↦ (input a).length) N) :
    PolyBounded (fun a ↦ (input a).length) fun a ↦ entB (σ a) (N a) := by
  unfold entB
  exact (((PolyBounded.const 7).mul (hN.mul (((PolyBounded.const 2).mul hσ).add (.const 1)))).add
    ((PolyBounded.const 2).mul hσ)).add (.const 9)

variable (c : Consts) {X : α → CoreIn}

theorem rdelS {p : α → ℕ} {f : α → ℚ} {pre : α → List (List AAtom)} {Hp : α → List AAtom}
    {st : α → List AAtom × List (List AAtom × Ctx.WKind)}
    (hX : ComputableInPolyTime X input encCI) (hp : ComputableInPolyTime p input encUnary)
    (hf : ComputableInPolyTime f input encRat) (hpre : ComputableInPolyTime pre input encSl)
    (hHp : ComputableInPolyTime Hp input encSq) (hst : ComputableInPolyTime st input encWS) :
    ComputableInPolyTime (fun a ↦ rdel (ctx c (X a)) (p a) (f a) (pre a) (Hp a) (st a)) input
      encWS := by
  have h1 : ComputableInPolyTime (fun a ↦ (st a).1) input encSq := (fst _ _).comp hst
  have h2 : ComputableInPolyTime (fun a ↦ (st a).2) input (encList encPt) := (snd _ _).comp hst
  have hq := cplU hHp h1
  have hz : ComputableInPolyTime (fun a ↦ ((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1)
      (0, 0)).1) input encNat := (fst _ _).comp (listGetDWithInput hHp hq (0, 0))
  have hc1 : ComputableInPolyTime (fun a ↦ (st a).1 ++
      [(((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1) (0, 0)).1, 1)]) input encSq :=
    listAppend' h1 (cons' (hz.prod (const 1)) (const []))
  have hinit := hc1.prod (listAppend' h2 (cons' (hc1.prod (wkAF hz)) (const [])))
  have hcnt := unary_sub' (lenL h1) hq
  have hstep : ComputableInPolyTime (fun q : α × (List AAtom × List (List AAtom × Ctx.WKind)) ↦
      (ctx c (X q.1)).delStep (p q.1) (f q.1) (pre q.1)
        (Ctx.commonPrefixLen (Hp q.1) (st q.1).1) q.2) (encPair input encWS) encWS :=
    delStepS c (hX.comp (fst _ _)) (hp.comp (fst _ _)) (hf.comp (fst _ _))
      (hpre.comp (fst _ _)) (hq.comp (fst _ _)) (snd _ _)
  -- the bounds
  let σ : α → ℕ := fun a ↦ (encSq (Hp a)).length + (encSq (st a).1).length +
    2 * (ctx c (X a)).ip.m + 3
  let N : α → ℕ := fun a ↦ (st a).1.length + (ctx c (X a)).ip.L + 1
  let P : α → AAtom → Prop := fun a y ↦ (encAt y).length ≤ σ a
  have hW (a : α) : WalkP (ctx c (X a)) (P a) (Hp a) (st a).1 := walkP_len _ _ _
  let init : α → List AAtom × List (List AAtom × Ctx.WKind) := fun a ↦
    ((st a).1 ++ [(((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1) (0, 0)).1, 1)],
      (st a).2 ++ [((st a).1 ++ [(((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1) (0, 0)).1,
        1)], .appendFree ((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1) (0, 0)).1)])
  have hc1P (a : α) : PSeq (P a) (N a) (init a).1 := by
    obtain ⟨hz1, -⟩ := getD_free (hW a) (Ctx.commonPrefixLen (Hp a) (st a).1)
    refine ⟨by simp [init, N], fun y hy ↦ ?_⟩
    rcases List.mem_append.1 hy with hy | hy
    · exact (hW a).start y hy
    · rw [List.mem_singleton.1 hy]; exact hz1
  have he0 (a : α) : PEnt (P a) (N a) ((init a).1, .appendFree
      ((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1) (0, 0)).1) :=
    ⟨hc1P a, (getD_free (hW a) _).2, pseq_nil _ _, pseq_nil _ _, pseq_nil _ _⟩
  have hsize : PolyBounded (fun a ↦ (input a).length) fun a ↦
      2 * (N a * (2 * σ a + 1)) + 1 + (encList encPt (st a).2).length +
        ((st a).1.length - Ctx.commonPrefixLen (Hp a) (st a).1 + 1) *
          (2 * entB (σ a) (N a) + 1) := by
    have hσ : PolyBounded (fun a ↦ (input a).length) σ :=
      ((hHp.polyBounded_length.add h1.polyBounded_length).add ((PolyBounded.const 2).mul
        (mU c hX).polyBounded)).add (.const 3)
    have hN : PolyBounded (fun a ↦ (input a).length) N :=
      ((lenL h1).polyBounded.add (LU c hX).polyBounded).add (.const 1)
    exact ((((PolyBounded.const 2).mul (hN.mul (((PolyBounded.const 2).mul hσ).add
      (.const 1)))).add (.const 1)).add h2.polyBounded_length).add ((hcnt.polyBounded.add
        (.const 1)).mul (((PolyBounded.const 2).mul (PolyBounded.entB' hσ hN)).add (.const 1)))
  have h := iterateWith_spec (par := fun a ↦ a)
    (count := fun a ↦ (st a).1.length - Ctx.commonPrefixLen (Hp a) (st a).1)
    (init := init)
    (step := fun a s ↦ (ctx c (X a)).delStep (p a) (f a) (pre a)
      (Ctx.commonPrefixLen (Hp a) (st a).1) s)
    id' hcnt hinit hstep
    (fun a i s ↦ PSeq (P a) (N a) s.1 ∧ ∃ new, s.2 = (init a).2 ++ new ∧ new.length ≤ i ∧
      ∀ e ∈ new, PEnt (P a) (N a) e)
    (fun a ↦ ⟨hc1P a, [], by simp, by simp, by simp⟩) ?_ hsize ?_
  · exact h.1
  · intro a i s _ ⟨hs, new, hnew, hlen, hent⟩
    obtain ⟨hs', e, he, hPe⟩ := delStep_inv (ctx c (X a)) (hW a).reg (hW a).zero (p a) (f a)
      (pre a) (Ctx.commonPrefixLen (Hp a) (st a).1) (N := N a) (by simp only [N]; omega) hs
    refine ⟨hs'.mono (by simp only [N]; omega), new ++ [e], by rw [he, hnew, List.append_assoc],
      by simp; omega, ?_⟩
    intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · exact hent e' he'
    · rw [List.mem_singleton.1 he']; exact hPe
  · intro a i s hi ⟨hs, new, hnew, hlen, hent⟩
    exact len_encWS_le (len_PSeq hs) hnew (len_PEnt (he0 a)) (len_ents hlen hent) hi

theorem roundBS {p : α → ℕ} {f : α → ℚ} {pre : α → List (List AAtom)} {Hp : α → List AAtom}
    {st : α → List AAtom × List (List AAtom × Ctx.WKind)}
    (hX : ComputableInPolyTime X input encCI) (hp : ComputableInPolyTime p input encUnary)
    (hf : ComputableInPolyTime f input encRat) (hpre : ComputableInPolyTime pre input encSl)
    (hHp : ComputableInPolyTime Hp input encSq) (hst : ComputableInPolyTime st input encWS) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).roundB (p a) (f a) (pre a) (Hp a) (st a)) input
      encWS := by
  simp only [roundB_eq]
  have h1 : ComputableInPolyTime (fun a ↦ (st a).1) input encSq := (fst _ _).comp hst
  have hq := cplU hHp h1
  have hz : ComputableInPolyTime (fun a ↦ ((Hp a).getD (Ctx.commonPrefixLen (Hp a) (st a).1)
      (0, 0)).1) input encNat := (fst _ _).comp (listGetDWithInput hHp hq (0, 0))
  have hr := rdelS c hX hp hf hpre hHp hst
  have h3 := setS ((fst _ _).comp hr) hq (hz.prod (const 0))
  exact ite' (isPrefixOfB hHp h1) hst
    (h3.prod (listAppend' ((snd _ _).comp hr) (cons' (h3.prod wkTR) (const []))))

theorem walkBS {p : α → ℕ} {f : α → ℚ} {pre : α → List (List AAtom)} {Hp H'p : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hp : ComputableInPolyTime p input encUnary)
    (hf : ComputableInPolyTime f input encRat) (hpre : ComputableInPolyTime pre input encSl)
    (hHp : ComputableInPolyTime Hp input encSq) (hH'p : ComputableInPolyTime H'p input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).walkB (p a) (f a) (pre a) (Hp a) (H'p a)) input
      (encList encPt) := by
  unfold Ctx.walkB
  have hstep : ComputableInPolyTime (fun q : α × (List AAtom × List (List AAtom × Ctx.WKind)) ↦
      (ctx c (X q.1)).roundB (p q.1) (f q.1) (pre q.1) (Hp q.1) q.2) (encPair input encWS)
      encWS :=
    roundBS c (hX.comp (fst _ _)) (hp.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _))
      (hHp.comp (fst _ _)) (snd _ _)
  have hinit : ComputableInPolyTime (fun a ↦ (H'p a, [(H'p a, Ctx.WKind.init)])) input encWS :=
    hH'p.prod (cons' (hH'p.prod wkInit) (const []))
  have hσ : PolyBounded (fun a ↦ (input a).length) fun a ↦
      (encSq (Hp a)).length + (encSq (H'p a)).length + 2 * (ctx c (X a)).ip.m + 3 :=
    ((hHp.polyBounded_length.add hH'p.polyBounded_length).add ((PolyBounded.const 2).mul
      (mU c hX).polyBounded)).add (.const 3)
  have hN : PolyBounded (fun a ↦ (input a).length) fun a ↦
      (H'p a).length + 2 * (ctx c (X a)).ip.L + 1 :=
    ((lenL hH'p).polyBounded.add ((PolyBounded.const 2).mul (LU c hX).polyBounded)).add (.const 1)
  have hK : PolyBounded (fun a ↦ (input a).length) fun a ↦
      1 + (ctx c (X a)).ip.L * ((H'p a).length + 2 * (ctx c (X a)).ip.L + 2) :=
    (PolyBounded.const 1).add ((LU c hX).polyBounded.mul (((lenL hH'p).polyBounded.add
      ((PolyBounded.const 2).mul (LU c hX).polyBounded)).add (.const 2)))
  have hsize := ((((PolyBounded.const 2).mul (hN.mul (((PolyBounded.const 2).mul hσ).add
    (.const 1)))).add (.const 1)).add (hK.mul (((PolyBounded.const 2).mul
      (PolyBounded.entB' hσ hN)).add (.const 1))))
  have h := iterateWith_spec (par := fun a ↦ a) (count := fun a ↦ (ctx c (X a)).ip.L)
    (init := fun a ↦ (H'p a, [(H'p a, Ctx.WKind.init)]))
    (step := fun a s ↦ (ctx c (X a)).roundB (p a) (f a) (pre a) (Hp a) s)
    id' (LU c hX) hinit hstep
    (fun a i s ↦ s = ((ctx c (X a)).roundB (p a) (f a) (pre a) (Hp a))^[i]
      (H'p a, [(H'p a, Ctx.WKind.init)]))
    (fun a ↦ rfl) (fun a i s _ hs ↦ by rw [hs, Function.iterate_succ_apply']) hsize ?_
  · exact (snd _ _).comp h.1
  · intro a i s hi hs
    rw [hs]
    obtain ⟨h1, h2, h3⟩ := walkB_inv (ctx c (X a)) (walkP_len (ctx c (X a)) (Hp a) (H'p a))
      (p a) (f a) (pre a) i hi
    have := Nat.mul_le_mul_right ((H'p a).length + 2 * (ctx c (X a)).ip.L + 2) hi
    exact len_encWS_le' h1 (by omega) (h2.trans (by omega)) h3

end BCFGJPSSV26.Greedy.PT


