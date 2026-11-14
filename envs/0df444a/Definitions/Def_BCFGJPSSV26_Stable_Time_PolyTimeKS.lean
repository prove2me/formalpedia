-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeKS
-- name    : BCFGJPSSV26_Stable_Time_PolyTimeKS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:24:00.57105+00:00
-- url     : https://prove2.me/theorems/312c9c20-db4a-4a52-bfde-9aa8d3b1243b
-- title:
--   BCFGJPSSV26.Stable.Time.PolyTimeKS — The cluster sampling in polynomial time
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.PolyTimeKS` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for the cluster sampling (`BCFGJPSSV26.Stable.ksRun`): one step
--   (`BCFGJPSSV26.Stable.PolyTime.ksStep'`) and the fold of `20 s + 20` steps. A step adds at most one
--   deleted center, of the local search or the center of the mode, and at most one dummy, led by the
--   center of the mode with a radius on the grid of a table entry; the center of the mode is one of
--   the local search (or `0`) and the radius base a table entry (or `0`). So along a run the states
--   grow by a bounded amount per step (`BCFGJPSSV26.Stable.PolyTime.KSSmall`).
--
--   **Contents.** The module is published as a whole: 30 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeKS`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/PolyTimeKS.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCoins

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.PolyTimeKS` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The cluster sampling in polynomial time

Certificates for the cluster sampling (`BCFGJPSSV26.Stable.ksRun`): one step
(`BCFGJPSSV26.Stable.PolyTime.ksStep'`) and the fold of `20 s + 20` steps. A step adds at most one
deleted center, of the local search or the center of the mode, and at most one dummy, led by the
center of the mode with a radius on the grid of a table entry; the center of the mode is one of
the local search (or `0`) and the radius base a table entry (or `0`). So along a run the states
grow by a bounded amount per step (`BCFGJPSSV26.Stable.PolyTime.KSSmall`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable.PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- The encoding of the states of the cluster sampling. -/
abbrev encKS : KSState ↪ List Bool :=
  encPair encNat (encPair encNat (encPair (encList encNat) (encPair (encList encDum)
    (encPair encNat (encPair encNat encRat)))))

theorem ksPhase' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).phase) input encNat := (fst _ _).comp h

theorem ksJ' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).j) input encNat := (fst _ _).comp ((snd _ _).comp h)

theorem ksDel' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).del) input (encList encNat) :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp h))

theorem ksDums' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).dums) input (encList encDum) :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp h)))

theorem ksTag' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).tag) input encNat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp h))))

theorem ksLdr' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).ldr) input encNat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    ((snd _ _).comp h)))))

theorem ksR₀' {st : α → KSState} (h : ComputableInPolyTime st input encKS) :
    ComputableInPolyTime (fun a ↦ (st a).r₀) input encRat :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
    ((snd _ _).comp h)))))

/-- A state from its seven components. -/
theorem ksMk' {ph j t l : α → ℕ} {del : α → List ℕ} {dums : α → List DumQ} {r : α → ℚ}
    (hph : ComputableInPolyTime ph input encNat) (hj : ComputableInPolyTime j input encNat)
    (hdel : ComputableInPolyTime del input (encList encNat))
    (hdums : ComputableInPolyTime dums input (encList encDum))
    (ht : ComputableInPolyTime t input encNat) (hl : ComputableInPolyTime l input encNat)
    (hr : ComputableInPolyTime r input encRat) :
    ComputableInPolyTime (fun a ↦ ((ph a, j a, del a, dums a, t a, l a, r a) : KSState)) input
      encKS :=
  hph.prod (hj.prod (hdel.prod (hdums.prod (ht.prod (hl.prod hr)))))

/-- The centers of `LS` not in `del`. -/
theorem filterNotMem' {LS del : α → List ℕ} (hLS : ComputableInPolyTime LS input (encList encNat))
    (hdel : ComputableInPolyTime del input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (LS a).filter fun c ↦ decide (c ∉ del a)) input
      (encList encNat) :=
  filterWithInput (test := fun a c ↦ decide (c ∉ del a)) hLS
    (decide_not (decide_mem (hdel.comp (fst _ _)) (snd _ _)))

theorem ksWeights' {x : α → Raw} {LS del cand : α → List ℕ} {Λ₁ dums : α → List DumQ}
    {ph : α → ℕ} (hx : ComputableInPolyTime x input encRaw)
    (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ₁ : ComputableInPolyTime Λ₁ input (encList encDum))
    (hph : ComputableInPolyTime ph input encNat)
    (hdel : ComputableInPolyTime del input (encList encNat))
    (hdums : ComputableInPolyTime dums input (encList encDum))
    (hcand : ComputableInPolyTime cand input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ ksWeights (x a) (LS a) (Λ₁ a) (ph a) (del a) (dums a)
      (cand a)) input (encList encRat) := by
  unfold ksWeights
  have hx' : ComputableInPolyTime (fun p : α × ℕ ↦ x p.1) (encPair input encNat) encRaw :=
    hx.comp (fst _ _)
  have h0 : ComputableInPolyTime (fun a ↦ (cand a).map fun c ↦
      (x a).costOn (LS a) ((x a).clusterQ (LS a) c)) input (encList encRat) :=
    mapWithInput (f := fun a c ↦ (x a).costOn (LS a) ((x a).clusterQ (LS a) c)) hcand
      (costOn' hx' (hLS.comp (fst _ _)) (clusterQ' hx' (fun p ↦ hn p.1) (hLS.comp (fst _ _))
        (snd _ _)))
  have hF : ComputableInPolyTime (fun p : α × ℕ ↦ (LS p.1).filter fun c ↦ decide (c ∉ del p.1))
      (encPair input encNat) (encList encNat) :=
    filterNotMem' (hLS.comp (fst _ _)) (hdel.comp (fst _ _))
  have hcl : ComputableInPolyTime (fun p : α × ℕ ↦ (x p.1).clusterMixQ
      ((LS p.1).filter fun c ↦ decide (c ∉ del p.1)) (Λ₁ p.1 ++ dums p.1) p.2)
      (encPair input encNat) (encList encNat) :=
    clusterMixQ' hx' (fun p ↦ hn p.1) hF (listAppend' (hΛ₁.comp (fst _ _))
      (hdums.comp (fst _ _))) (snd _ _)
  have h1 : ComputableInPolyTime (fun a ↦ (cand a).map fun c ↦
      (((x a).clusterMixQ ((LS a).filter fun c' ↦ decide (c' ∉ del a)) (Λ₁ a ++ dums a) c).map
        fun y ↦ (x a).fdist y c).sum) input (encList encRat) :=
    mapWithInput (f := fun a c ↦ (((x a).clusterMixQ ((LS a).filter fun c' ↦ decide (c' ∉ del a))
      (Λ₁ a ++ dums a) c).map fun y ↦ (x a).fdist y c).sum) hcand
      (rat_sum' (mapWithInput (f := fun (p : α × ℕ) y ↦ (x p.1).fdist y p.2) hcl
        (fdist' (hx.comp ((fst _ _).comp (fst _ _))) (snd _ _) ((snd _ _).comp (fst _ _)))))
  exact ite_decide (decide_eq' hph (const 0)) h0 h1

/-- The candidates of the mode `SAMPLE`. -/
def ksCand (LS : List ℕ) (st : KSState) : List ℕ := LS.filter fun c ↦ decide (c ∉ st.del)

/-- The candidates of the mode `DG`. -/
def ksCand' (LS : List ℕ) (st : KSState) : List ℕ :=
  LS.filter fun c ↦ decide (c ∉ st.del ∧ c ≠ st.ldr)

/-- One step of the cluster sampling, with the projections of the state. -/
theorem ksStep_eq (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ) (st : KSState)
    (u : ℕ) : ksStep N x LS Λ₁ s b st u =
    if st.phase = 2 then st
    else if st.tag = 0 then
      if st.j = s then
        (if st.phase = 0 then (1, 0, st.del, st.dums, 0, st.ldr, st.r₀)
          else (2, 0, st.del, st.dums, 0, st.ldr, st.r₀))
      else if cbit b u then (st.phase, st.j + 1, st.del, st.dums, 0, st.ldr, st.r₀)
      else (st.phase, st.j, st.del, st.dums, 1, st.ldr, st.r₀)
    else if st.tag = 1 then
      if ksCand LS st = [] then (st.phase, st.j + 1, st.del, st.dums, 0, st.ldr, st.r₀)
      else (st.phase, st.j, st.del, st.dums, 2, (ksCand LS st).getD
        (wsample b (ksWeights x LS Λ₁ st.phase st.del st.dums (ksCand LS st)) u) 0, st.r₀)
    else if st.tag = 2 then
      if st.del.length ≤ s ∧ cbit b u = true then
        (st.phase, st.j + 1, st.del ++ [st.ldr], st.dums, 0, st.ldr, st.r₀)
      else (st.phase, st.j, st.del, st.dums, 3, st.ldr, st.r₀)
    else if st.tag = 3 then
      if 2 * s < st.dums.length + st.del.length then
        (st.phase, st.j + 1, st.del, st.dums, 0, st.ldr, st.r₀)
      else if ksCand' LS st = [] then (st.phase, st.j + 1, st.del, st.dums, 0, st.ldr, st.r₀)
      else if cbit b u then (st.phase, st.j, st.del, st.dums, 4, st.ldr,
        x.fdist (x.n + st.ldr) (x.nearQ (x.n + st.ldr) (ksCand' LS st)))
      else (st.phase, st.j, st.del ++ [x.nearQ (x.n + st.ldr) (ksCand' LS st)], st.dums, 3,
        st.ldr, st.r₀)
    else if st.tag = 4 then
      if 2 * s < st.dums.length + st.del.length then
        (st.phase, st.j + 1, st.del ++ [st.ldr], st.dums, 0, st.ldr, st.r₀)
      else (st.phase, st.j, st.del, st.dums ++
        [(x.n + st.ldr, ksRad N s st.r₀ (cunif (Par.Gr N) u) st.dums.length)], 5, st.ldr, st.r₀)
    else
      if cbit b u then (st.phase, st.j + 1, st.del ++ [st.ldr], st.dums, 0, st.ldr, st.r₀)
      else (st.phase, st.j, st.del, st.dums, 4, st.ldr, st.r₀) := by
  rfl

theorem ksRad_eq (N s : ℕ) (r₀ : ℚ) (v t : ℕ) :
    ksRad N s r₀ v t = grid N r₀ v + r₀ * ((t : ℕ) : ℚ) / (((N ^ 4 : ℕ) : ℚ) *
      (2 * ((s : ℕ) : ℚ) + 2)) := by
  unfold ksRad
  push_cast
  rfl

/-- The radius of a dummy of the cluster sampling. -/
theorem ksRad' {N s u t : α → ℕ} {r : α → ℚ} (hN : ComputableInPolyTime N input encUnary)
    (hs : ComputableInPolyTime s input encNat) (hr : ComputableInPolyTime r input encRat)
    (hu : ComputableInPolyTime u input encNat) (ht : ComputableInPolyTime t input encNat) :
    ComputableInPolyTime (fun a ↦ ksRad (N a) (s a) (r a) (cunif (Par.Gr (N a)) (u a)) (t a))
      input encRat := by
  simp only [ksRad_eq]
  exact rat_add' (grid' hN hr hu) (rat_div' (rat_mul' hr (rat_natCast' ht))
    (rat_mul' (rat_natCast' (binary_pow' (unary_to_binary.comp hN) (const 4)))
      (rat_add' (rat_mul' (const 2) (rat_natCast' hs)) (const 2))))

/-- **One step of the cluster sampling.** -/
theorem ksStep' {N s b u : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {Λ₁ : α → List DumQ}
    {st : α → KSState} (hN : ComputableInPolyTime N input encUnary)
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ₁ : ComputableInPolyTime Λ₁ input (encList encDum))
    (hs : ComputableInPolyTime s input encNat) (hb : ComputableInPolyTime b input encUnary)
    (hst : ComputableInPolyTime st input encKS) (hu : ComputableInPolyTime u input encNat) :
    ComputableInPolyTime (fun a ↦ ksStep (N a) (x a) (LS a) (Λ₁ a) (s a) (b a) (st a) (u a))
      input encKS := by
  simp only [ksStep_eq]
  have hph := ksPhase' hst
  have hj := ksJ' hst
  have hdel := ksDel' hst
  have hdums := ksDums' hst
  have htag := ksTag' hst
  have hl := ksLdr' hst
  have hr := ksR₀' hst
  have hj1 : ComputableInPolyTime (fun a ↦ (st a).j + 1) input encNat := binAdd' hj (const 1)
  have hbit := cbit' hb hu
  have hdl : ComputableInPolyTime (fun a ↦ (st a).del ++ [(st a).ldr]) input (encList encNat) :=
    listAppend' hdel (cons' hl (const []))
  have hlen : ComputableInPolyTime (fun a ↦ (st a).dums.length + (st a).del.length) input
      encNat :=
    binAdd' (unary_to_binary.comp ((length_list encDum).comp hdums))
      (unary_to_binary.comp ((length_list encNat).comp hdel))
  have hfull := binary_lt' (binMul' (const 2) hs) hlen
  -- tag 0
  have h0 : ComputableInPolyTime (fun a ↦
      if (st a).j = s a then
        (if (st a).phase = 0 then ((1, 0, (st a).del, (st a).dums, 0, (st a).ldr, (st a).r₀) :
          KSState) else (2, 0, (st a).del, (st a).dums, 0, (st a).ldr, (st a).r₀))
      else if cbit (b a) (u a) then ((st a).phase, (st a).j + 1, (st a).del, (st a).dums, 0,
        (st a).ldr, (st a).r₀)
      else ((st a).phase, (st a).j, (st a).del, (st a).dums, 1, (st a).ldr, (st a).r₀))
      input encKS :=
    ite_decide (decide_eq' hj hs)
      (ite_decide (decide_eq' hph (const 0)) (ksMk' (const 1) (const 0) hdel hdums (const 0) hl hr)
        (ksMk' (const 2) (const 0) hdel hdums (const 0) hl hr))
      (ite' hbit (ksMk' hph hj1 hdel hdums (const 0) hl hr)
        (ksMk' hph hj hdel hdums (const 1) hl hr))
  -- tag 1
  have hcand : ComputableInPolyTime (fun a ↦ ksCand (LS a) (st a)) input (encList encNat) := by
    unfold ksCand
    exact filterNotMem' hLS hdel
  have hcandE : ComputableInPolyTime (fun a ↦ decide (ksCand (LS a) (st a) = [])) input
      encBool :=
    ((listIsEmpty (encA := encNat)).comp hcand).of_enc_eq fun a ↦ by
      change encBool (decide (ksCand (LS a) (st a) = [])) = encBool (ksCand (LS a) (st a)).isEmpty
      cases ksCand (LS a) (st a) <;> rfl
  have hw := ksWeights' hx hn hLS hΛ₁ hph hdel hdums hcand
  have h1 : ComputableInPolyTime (fun a ↦
      if ksCand (LS a) (st a) = [] then
        (((st a).phase, (st a).j + 1, (st a).del, (st a).dums, 0, (st a).ldr, (st a).r₀) : KSState)
      else ((st a).phase, (st a).j, (st a).del, (st a).dums, 2, (ksCand (LS a) (st a)).getD
        (wsample (b a) (ksWeights (x a) (LS a) (Λ₁ a) (st a).phase (st a).del (st a).dums
          (ksCand (LS a) (st a))) (u a)) 0, (st a).r₀)) input encKS :=
    ite_decide hcandE (ksMk' hph hj1 hdel hdums (const 0) hl hr)
      (ksMk' hph hj hdel hdums (const 2) (listGetD_binary (encA := encNat) 0 hcand
        (wsample' hb hw hu)) hr)
  -- tag 2
  have h2 : ComputableInPolyTime (fun a ↦
      if (st a).del.length ≤ s a ∧ cbit (b a) (u a) = true then
        (((st a).phase, (st a).j + 1, (st a).del ++ [(st a).ldr], (st a).dums, 0, (st a).ldr,
          (st a).r₀) : KSState)
      else ((st a).phase, (st a).j, (st a).del, (st a).dums, 3, (st a).ldr, (st a).r₀))
      input encKS :=
    ite_decide (decide_and (binary_le' (unary_to_binary.comp ((length_list encNat).comp hdel)) hs)
        (decide_eq' hbit (const true)))
      (ksMk' hph hj1 hdl hdums (const 0) hl hr) (ksMk' hph hj hdel hdums (const 3) hl hr)
  -- tag 3
  have hcand' : ComputableInPolyTime (fun a ↦ ksCand' (LS a) (st a)) input (encList encNat) := by
    unfold ksCand'
    exact filterWithInput (test := fun a c ↦ decide (c ∉ (st a).del ∧ c ≠ (st a).ldr)) hLS
      (decide_and (decide_not (decide_mem (hdel.comp (fst _ _)) (snd _ _)))
        (decide_not (decide_eq' (snd _ _) (hl.comp (fst _ _)))))
  have hcandE' : ComputableInPolyTime (fun a ↦ decide (ksCand' (LS a) (st a) = [])) input
      encBool :=
    ((listIsEmpty (encA := encNat)).comp hcand').of_enc_eq fun a ↦ by
      change encBool (decide (ksCand' (LS a) (st a) = [])) =
        encBool (ksCand' (LS a) (st a)).isEmpty
      cases ksCand' (LS a) (st a) <;> rfl
  have hnl : ComputableInPolyTime (fun a ↦ (x a).n + (st a).ldr) input encNat :=
    binAdd' (raw_n' hx) hl
  have hc' := nearQ' hx hnl hcand'
  have h3 : ComputableInPolyTime (fun a ↦
      if 2 * s a < (st a).dums.length + (st a).del.length then
        (((st a).phase, (st a).j + 1, (st a).del, (st a).dums, 0, (st a).ldr, (st a).r₀) : KSState)
      else if ksCand' (LS a) (st a) = [] then
        ((st a).phase, (st a).j + 1, (st a).del, (st a).dums, 0, (st a).ldr, (st a).r₀)
      else if cbit (b a) (u a) then ((st a).phase, (st a).j, (st a).del, (st a).dums, 4,
        (st a).ldr, (x a).fdist ((x a).n + (st a).ldr)
          ((x a).nearQ ((x a).n + (st a).ldr) (ksCand' (LS a) (st a))))
      else ((st a).phase, (st a).j, (st a).del ++ [(x a).nearQ ((x a).n + (st a).ldr)
        (ksCand' (LS a) (st a))], (st a).dums, 3, (st a).ldr, (st a).r₀)) input encKS :=
    ite_decide hfull (ksMk' hph hj1 hdel hdums (const 0) hl hr)
      (ite_decide hcandE' (ksMk' hph hj1 hdel hdums (const 0) hl hr)
        (ite' hbit (ksMk' hph hj hdel hdums (const 4) hl (fdist' hx hnl hc'))
          (ksMk' hph hj (listAppend' hdel (cons' hc' (const []))) hdums (const 3) hl hr)))
  -- tag 4
  have hdum : ComputableInPolyTime (fun a ↦ ((x a).n + (st a).ldr, ksRad (N a) (s a) (st a).r₀
      (cunif (Par.Gr (N a)) (u a)) (st a).dums.length)) input encDum :=
    hnl.prod (ksRad' hN hs hr hu (unary_to_binary.comp ((length_list encDum).comp hdums)))
  have h4 : ComputableInPolyTime (fun a ↦
      if 2 * s a < (st a).dums.length + (st a).del.length then
        (((st a).phase, (st a).j + 1, (st a).del ++ [(st a).ldr], (st a).dums, 0, (st a).ldr,
          (st a).r₀) : KSState)
      else ((st a).phase, (st a).j, (st a).del, (st a).dums ++
        [((x a).n + (st a).ldr, ksRad (N a) (s a) (st a).r₀ (cunif (Par.Gr (N a)) (u a))
          (st a).dums.length)], 5, (st a).ldr, (st a).r₀)) input encKS :=
    ite_decide hfull (ksMk' hph hj1 hdl hdums (const 0) hl hr)
      (ksMk' hph hj hdel (listAppend' hdums (cons' hdum (const []))) (const 5) hl hr)
  -- tag 5
  have h5 : ComputableInPolyTime (fun a ↦
      if cbit (b a) (u a) then
        (((st a).phase, (st a).j + 1, (st a).del ++ [(st a).ldr], (st a).dums, 0, (st a).ldr,
          (st a).r₀) : KSState)
      else ((st a).phase, (st a).j, (st a).del, (st a).dums, 4, (st a).ldr, (st a).r₀))
      input encKS :=
    ite' hbit (ksMk' hph hj1 hdl hdums (const 0) hl hr) (ksMk' hph hj hdel hdums (const 4) hl hr)
  exact ite_decide (decide_eq' hph (const 2)) hst
    (ite_decide (decide_eq' htag (const 0)) h0
      (ite_decide (decide_eq' htag (const 1)) h1
        (ite_decide (decide_eq' htag (const 2)) h2
          (ite_decide (decide_eq' htag (const 3)) h3
            (ite_decide (decide_eq' htag (const 4)) h4 h5)))))

/-! ### The sizes of the states -/

/-- The states reached after `i` steps: their lists have at most `i` entries, of sizes at most
`λ` (centers) and `δ` (dummies), and the radius base has size at most `ρ`. -/
def KSSmall (lam ρ δ i : ℕ) (st : KSState) : Prop :=
  st.phase ≤ 2 ∧ st.tag ≤ 5 ∧ st.j ≤ i ∧ st.del.length ≤ i ∧ st.dums.length ≤ i ∧
    (encNat st.ldr).length ≤ lam ∧ (encRat st.r₀).length ≤ ρ ∧
    (∀ c ∈ st.del, (encNat c).length ≤ lam) ∧ ∀ d ∈ st.dums, (encDum d).length ≤ δ

theorem nearQ_mem_or (x : Raw) (a : ℕ) (S : List ℕ) : x.nearQ a S ∈ S ∨ x.nearQ a S = 0 := by
  unfold Raw.nearQ
  cases h : S.find? _ with
  | none => exact .inr rfl
  | some c => exact .inl (List.mem_of_find?_eq_some h)

theorem getD_mem_or (l : List ℕ) (k : ℕ) : l.getD k 0 ∈ l ∨ l.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact .inr rfl
  | some c => exact .inl (List.mem_of_getElem? h)

theorem length_encRat_zero : (encRat (0 : ℚ)).length = 4 := rfl

theorem length_encRat_dist_le (x : Raw) (p q : ℕ) :
    (encRat (x.dist p q)).length ≤ (encRaw x).length + 4 := by
  unfold Raw.dist
  have hT : (encList (encList encRat) x.table).length ≤ (encRaw x).length := by
    change _ ≤ (encPair encNat (encPair encNat (encPair encNat (encList (encList encRat))))
      (x.1, x.2.1, x.2.2.1, x.2.2.2)).length
    simp only [length_encPair]
    unfold Raw.table
    omega
  rw [List.getD_eq_getElem?_getD]
  cases h : (x.table.getD p [])[q]? with
  | none => simp [length_encRat_zero]
  | some e =>
    have he := List.mem_of_getElem? h
    have hrow : (encList encRat (x.table.getD p [])).length ≤ (encRaw x).length := by
      rw [List.getD_eq_getElem?_getD]
      cases h' : x.table[p]? with
      | none => simp
      | some r =>
        exact (SizedListEncoding.length_elem_le (encA := encList encRat)
          (encL := encList (encList encRat)) _ _ (List.mem_of_getElem? h')).trans hT
    have := SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) _ _ he
    simp only [Option.getD_some]
    omega

theorem forall_mem_append_singleton {β : Type} {P : β → Prop} {l : List β} {a : β}
    (hl : ∀ c ∈ l, P c) (ha : P a) : ∀ c ∈ l ++ [a], P c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hl c hc
  · rw [List.mem_singleton.1 hc]
    exact ha

theorem length_append_singleton_le {β : Type} {l : List β} {i : ℕ} (h : l.length ≤ i) (a : β) :
    (l ++ [a]).length ≤ i + 1 := by
  rw [List.length_append, List.length_singleton]
  omega

/-- **The states stay small**: one step from a state reached after `i` steps. -/
theorem ksStep_small {N : ℕ} {x : Raw} {LS : List ℕ} {Λ₁ : List DumQ} {s b u lam ρ δ i M : ℕ}
    (hLS : ∀ c ∈ LS, (encNat c).length ≤ lam)
    (hρ : ∀ p q, (encRat (x.dist p q)).length ≤ ρ)
    (hδ : ∀ l r v t, (encNat l).length ≤ lam → (encRat r).length ≤ ρ → v < Par.Gr N →
      t ≤ M → (encDum (x.n + l, ksRad N s r v t)).length ≤ δ)
    (hiM : i < M) {st : KSState} (h : KSSmall lam ρ δ i st) :
    KSSmall lam ρ δ (i + 1) (ksStep N x LS Λ₁ s b st u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have h0 : (encNat 0).length ≤ lam := Nat.zero_le _
  have hget : ∀ k, (encNat ((ksCand LS st).getD k 0)).length ≤ lam := by
    intro k
    rcases getD_mem_or (ksCand LS st) k with hk | hk
    · exact hLS _ (List.mem_of_mem_filter hk)
    · rw [hk]
      exact h0
  have hnear : (encNat (x.nearQ (x.n + st.ldr) (ksCand' LS st))).length ≤ lam := by
    rcases nearQ_mem_or x (x.n + st.ldr) (ksCand' LS st) with hk | hk
    · exact hLS _ (List.mem_of_mem_filter hk)
    · rw [hk]
      exact h0
  have hfd : ∀ c, (encRat (x.fdist (x.n + st.ldr) c)).length ≤ ρ := fun c ↦ hρ _ _
  have hdum : (encDum (x.n + st.ldr, ksRad N s st.r₀ (cunif (Par.Gr N) u)
      st.dums.length)).length ≤ δ :=
    hδ _ _ _ _ h6 h7 (Nat.mod_lt _ (by unfold Par.Gr; omega)) (by omega)
  have hj1 : st.j + 1 ≤ i + 1 := by omega
  have hj2 : st.j ≤ i + 1 := by omega
  have hd1 : st.del.length ≤ i + 1 := by omega
  have hd2 : st.dums.length ≤ i + 1 := by omega
  have hA := forall_mem_append_singleton h8 h6
  have hB := forall_mem_append_singleton h8 hnear
  have hC := forall_mem_append_singleton h9 hdum
  have hD := length_append_singleton_le h4 st.ldr
  have hE := length_append_singleton_le h4 (x.nearQ (x.n + st.ldr) (ksCand' LS st))
  have hF := length_append_singleton_le h5
    (x.n + st.ldr, ksRad N s st.r₀ (cunif (Par.Gr N) u) st.dums.length)
  rw [ksStep_eq]
  split_ifs
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · first | exact h1 | exact Nat.le_of_ble_eq_true rfl
    · first | exact h2 | exact Nat.le_of_ble_eq_true rfl
    · first | exact hj1 | exact hj2 | exact Nat.zero_le _
    · first | exact hd1 | exact hD | exact hE
    · first | exact hd2 | exact hF
    · first | exact h6 | exact hget _
    · first | exact h7 | exact hfd _
    · first | exact h8 | exact hA | exact hB
    · first | exact h9 | exact hC

/-- A dummy of the cluster sampling, from `(n, l, N, s, r₀, v, t)`. -/
def ksDumOf (z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ) : DumQ :=
  (z.1 + z.2.1, ksRad z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2)

/-- The encoding of the arguments of `BCFGJPSSV26.Stable.PolyTime.ksDumOf`. -/
abbrev encDz : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encUnary (encPair encUnary (encPair encRat
    (encPair encUnary encUnary)))))

theorem ksDumOf_polytime : ComputableInPolyTime ksDumOf encDz encDum := by
  unfold ksDumOf
  simp only [ksRad_eq]
  have hN : ComputableInPolyTime (fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦ z.2.2.1) encDz encUnary :=
    (fst _ _).comp ((snd _ _).comp (snd _ _))
  have hs : ComputableInPolyTime (fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦ z.2.2.2.1) encDz
      encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _)))
  have hr : ComputableInPolyTime (fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦ z.2.2.2.2.1) encDz
      encRat := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
  have hv : ComputableInPolyTime (fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦ z.2.2.2.2.2.1) encDz
      encUnary := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
        ((snd _ _).comp (snd _ _)))))
  have ht : ComputableInPolyTime (fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦ z.2.2.2.2.2.2) encDz
      encUnary := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp
        ((snd _ _).comp (snd _ _)))))
  exact (binAdd' (fst _ _) ((fst _ _).comp (snd _ _))).prod
    (rat_add' (grid_polytime.comp (g := fun z : ℕ × ℕ × ℕ × ℕ × ℚ × ℕ × ℕ ↦
      (z.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2.1)) (hN.prod (hr.prod hv)))
      (rat_div' (rat_mul' hr (rat_natCast' (unary_to_binary.comp ht)))
        (rat_mul' (rat_natCast' (binary_pow' (unary_to_binary.comp hN) (const 4)))
          (rat_add' (rat_mul' (const 2) (rat_natCast' (unary_to_binary.comp hs))) (const 2)))))

/-- The size of the states after `i ≤ M` steps. -/
theorem length_encKS_le {lam ρ δ i M : ℕ} {st : KSState} (h : KSSmall lam ρ δ i st)
    (hi : i ≤ M) :
    (encKS st).length ≤ 2 * 2 + 1 + (2 * M + 1) + (2 * (M * (2 * lam + 1)) + 1) +
      (2 * (M * (2 * δ + 1)) + 1) + (2 * 5 + 1) + (2 * lam + 1) + ρ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have e : (encKS st).length = 2 * (encNat st.phase).length + 1 + (2 * (encNat st.j).length + 1 +
      (2 * (encList encNat st.del).length + 1 + (2 * (encList encDum st.dums).length + 1 +
        (2 * (encNat st.tag).length + 1 + (2 * (encNat st.ldr).length + 1 +
          (encRat st.r₀).length))))) := by
    simp only [length_encPair]
    rfl
  have hp := (length_encNat_le st.phase).trans h1
  have hj := (length_encNat_le st.j).trans (h3.trans hi)
  have ht := (length_encNat_le st.tag).trans h2
  have hd : (encList encNat st.del).length ≤ M * (2 * lam + 1) :=
    (length_encList_le encNat st.del h8).trans (Nat.mul_le_mul_right _ (h4.trans hi))
  have hm : (encList encDum st.dums).length ≤ M * (2 * δ + 1) :=
    (length_encList_le encDum st.dums h9).trans (Nat.mul_le_mul_right _ (h5.trans hi))
  omega

/-- **The cluster sampling**, when the clients are at most the rows of the table. -/
theorem ksRun' {N s b : α → ℕ} {x : α → Raw} {LS : α → List ℕ} {Λ₁ : α → List DumQ}
    {ch : α → ℕ → ℕ} (hN : ComputableInPolyTime N input encUnary)
    (hx : ComputableInPolyTime x input encRaw) (hn : ∀ a, (x a).n ≤ (x a).table.length)
    (hLS : ComputableInPolyTime LS input (encList encNat))
    (hΛ₁ : ComputableInPolyTime Λ₁ input (encList encDum))
    (hs : ComputableInPolyTime s input encUnary) (hb : ComputableInPolyTime b input encUnary)
    (hch : ChAcc input ch) :
    ComputableInPolyTime (fun a ↦ ksRun (N a) (x a) (LS a) (Λ₁ a) (s a) (b a) (ch a)) input
      encKS := by
  unfold ksRun
  obtain ⟨cδ, dδ, hδ⟩ := exists_le_pow ksDumOf_polytime.polyBounded_length
  set lam : α → ℕ := fun a ↦ (encList encNat (LS a)).length
  set ρ : α → ℕ := fun a ↦ (encRaw (x a)).length + 4
  set M : α → ℕ := fun a ↦ 20 * s a + 20
  set W : α → ℕ := fun a ↦ 2 * (encNat (x a).n).length + 2 * lam a + 2 * N a + 2 * s a +
    2 * ρ a + 2 * Par.Gr (N a) + M a + 7
  set δ : α → ℕ := fun a ↦ cδ * W a ^ dδ
  have hstep : ComputableInPolyTime (fun p : (α × KSState) × ℕ ↦ ksStep (N p.1.1) (x p.1.1)
      (LS p.1.1) (Λ₁ p.1.1) (s p.1.1) (b p.1.1) p.1.2 (ch p.1.1 p.2))
      (encPair (encPair input encKS) encUnary) encKS :=
    ksStep' (hN.comp ((fst _ _).comp (fst _ _))) (hx.comp ((fst _ _).comp (fst _ _)))
      (fun p ↦ hn p.1.1) (hLS.comp ((fst _ _).comp (fst _ _)))
      (hΛ₁.comp ((fst _ _).comp (fst _ _)))
      (unary_to_binary.comp (hs.comp ((fst _ _).comp (fst _ _))))
      (hb.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _))
      (chAt (hch.comp' ((fst _ _).comp (fst _ _))) (unary_to_binary.comp (snd _ _)))
  have hinit : ComputableInPolyTime (fun _ : α ↦ ksInit) input encKS := const _
  refine (foldlWith_spec (par := fun a ↦ a) (list := fun a ↦ List.range (20 * s a + 20))
    (init := fun _ ↦ ksInit)
    (step := fun a st t ↦ ksStep (N a) (x a) (LS a) (Λ₁ a) (s a) (b a) st (ch a t))
    id' (unary_range' (unary_add' (unary_mul' (const 20) hs) (const 20))) hinit hstep
    (fun a consumed st ↦ KSSmall (lam a) (ρ a) (δ a) consumed.length st)
    (fun a ↦ ?_) (fun a consumed st t hpre hst ↦ ?_)
    (size := fun a ↦ 2 * 2 + 1 + (2 * M a + 1) + (2 * (M a * (2 * lam a + 1)) + 1) +
      (2 * (M a * (2 * δ a + 1)) + 1) + (2 * 5 + 1) + (2 * lam a + 1) + ρ a) ?_
    (fun a consumed st hpre hst ↦ ?_)).1
  · -- the initial state
    refine ⟨Nat.zero_le _, Nat.zero_le _, le_rfl, le_rfl, le_rfl, Nat.zero_le _, ?_,
      fun c hc ↦ by simp [ksInit, KSState.del] at hc,
      fun d hd ↦ by simp [ksInit, KSState.dums] at hd⟩
    change (encRat 0).length ≤ (encRaw (x a)).length + 4
    rw [length_encRat_zero]
    omega
  · -- one step
    have hlen : consumed.length < 20 * s a + 20 := by
      have := hpre.length_le
      simp only [List.length_append, List.length_singleton, List.length_range] at this
      omega
    rw [List.length_append, List.length_singleton]
    refine ksStep_small (M := M a) (fun c hc ↦ ?_) (fun p q ↦ length_encRat_dist_le _ p q)
      (fun l r v t hl hr hv ht ↦ ?_) hlen hst
    · exact SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) _ _ hc
    · have h := hδ ((x a).n, l, N a, s a, r, v, t)
      have hz : (encDz ((x a).n, l, N a, s a, r, v, t)).length + 1 ≤ W a := by
        simp only [encDz, length_encPair, encUnary_apply, List.length_replicate]
        simp only [W, M, ρ, lam] at hl hr ht ⊢
        omega
      exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hz _))
  · have pN := hN.polyBounded
    have ps := hs.polyBounded
    have pl : PolyBounded (fun a ↦ (input a).length) lam := hLS.polyBounded_length
    have pρ : PolyBounded (fun a ↦ (input a).length) ρ := hx.polyBounded_length.add (.const 4)
    have pM : PolyBounded (fun a ↦ (input a).length) M := ((PolyBounded.const 20).mul ps).add
      (.const 20)
    have pG : PolyBounded (fun a ↦ (input a).length) fun a ↦ Par.Gr (N a) :=
      (((PolyBounded.const 10).mul (pN.mul pN)).add (.const 1)).mono fun a ↦ by
        unfold Par.Gr
        rw [sq]
    have pn : PolyBounded (fun a ↦ (input a).length) fun a ↦ (encNat (x a).n).length :=
      (raw_n' hx).polyBounded_length
    have pW : PolyBounded (fun a ↦ (input a).length) W :=
      ((((((((PolyBounded.const 2).mul pn).add ((PolyBounded.const 2).mul pl)).add
        ((PolyBounded.const 2).mul pN)).add ((PolyBounded.const 2).mul ps)).add
          ((PolyBounded.const 2).mul pρ)).add ((PolyBounded.const 2).mul pG)).add pM).add
            (.const 7)
    have pδ : PolyBounded (fun a ↦ (input a).length) δ := (PolyBounded.const cδ).mul (pW.pow dδ)
    exact ((((((PolyBounded.const (2 * 2 + 1)).add (((PolyBounded.const 2).mul pM).add
      (.const 1))).add (((PolyBounded.const 2).mul (pM.mul (((PolyBounded.const 2).mul pl).add
        (.const 1)))).add (.const 1))).add (((PolyBounded.const 2).mul (pM.mul
          (((PolyBounded.const 2).mul pδ).add (.const 1)))).add (.const 1))).add
            (.const (2 * 5 + 1))).add (((PolyBounded.const 2).mul pl).add (.const 1))).add pρ
  · exact length_encKS_le hst (by
      have := hpre.length_le
      simp only [List.length_range] at this
      exact this)

end BCFGJPSSV26.Stable.PolyTime


