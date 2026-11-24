-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
-- name    : Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:34.263737+00:00
-- url     : https://prove2.me/theorems/c230fe2a-998d-434f-895e-a4f7ec8c2d69
-- title:
--   Kernel-checked coloring and branching clique certificates
-- statement:
--   Defines finite cliques and membership in a natural bit mask, an independent-class check, a coloring cover check, and a recursive certificate with coloring leaves and include/exclude splits. Its proved soundness lemmas show that a successful check bounds every clique contained in the mask. The maskOf construction is proved to have exactly the listed vertices as its set bits.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/CliqueCertificate.lean lines 18–150; SHA256 f0ac51c4a85a54f800b3b22ed5eacf85f9f0a5b3cae5cc6b37ddeb04a758ddae; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate



/-!
# A kernel-checkable branch and coloring certificate

Vertices are natural numbers and each adjacency row is a bit mask. A terminal
certificate covers the candidate mask by explicitly listed independent color
classes. A branch separates cliques containing a chosen vertex from cliques
that omit it. The soundness theorem bounds the cardinality of every actual
finite clique in the candidate mask.
-/

namespace SensitivityCliqueCertificate

def maskOf : List ℕ → ℕ
  | [] => 0
  | v :: rest => 2 ^ v ||| maskOf rest

theorem testBit_maskOf (vertices : List ℕ) (v : ℕ) :
    (maskOf vertices).testBit v = true ↔ v ∈ vertices := by
  induction vertices with
  | nil => simp [maskOf]
  | cons a rest ih =>
    rw [maskOf, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

def Clique (adj : ℕ → ℕ) (vertices : Finset ℕ) : Prop :=
  ∀ v ∈ vertices, ∀ w ∈ vertices, v ≠ w → (adj v).testBit w = true

def InMask (mask : ℕ) (vertices : Finset ℕ) : Prop :=
  ∀ v ∈ vertices, mask.testBit v = true

def independentCheck (adj : ℕ → ℕ) (vertices : List ℕ) : Bool :=
  let mask := maskOf vertices
  vertices.all (fun v => decide (adj v &&& mask = 0))

theorem independentCheck_sound {adj : ℕ → ℕ} {vertices : List ℕ}
    (hcheck : independentCheck adj vertices = true)
    {v w : ℕ} (hv : v ∈ vertices) (hw : w ∈ vertices) :
    (adj v).testBit w = false := by
  have hall := List.all_eq_true.mp hcheck
  have hzero : adj v &&& maskOf vertices = 0 := of_decide_eq_true (hall v hv)
  have hbits := congrArg (fun n => n.testBit w) hzero
  have hwbit := (testBit_maskOf vertices w).mpr hw
  simpa only [Nat.testBit_and, hwbit, Bool.and_true, Nat.zero_testBit] using hbits

theorem coloring_bound (adj : ℕ → ℕ) (classes : List (List ℕ))
    (hgood : ∀ group ∈ classes, independentCheck adj group = true)
    (vertices : Finset ℕ) (hclique : Clique adj vertices)
    (hcover : ∀ v ∈ vertices, v ∈ classes.flatten) :
    vertices.card ≤ classes.length := by
  induction classes generalizing vertices with
  | nil =>
    have hempty : vertices = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      simpa using hcover v hv
    simp [hempty]
  | cons group rest ih =>
    let inside := vertices.filter (fun v => v ∈ group)
    let outside := vertices.filter (fun v => v ∉ group)
    have hinside : inside.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro v hv w hw
      have hvm := Finset.mem_filter.mp hv
      have hwm := Finset.mem_filter.mp hw
      by_contra hne
      have hfalse := independentCheck_sound
        (hgood group (List.mem_cons_self)) hvm.2 hwm.2
      have htrue := hclique v hvm.1 w hwm.1 hne
      rw [hfalse] at htrue
      contradiction
    have houtside : outside.card ≤ rest.length := by
      apply ih
      · intro next hnext
        exact hgood next (List.mem_cons_of_mem _ hnext)
      · intro v hv w hw hne
        exact hclique v (Finset.mem_filter.mp hv).1 w (Finset.mem_filter.mp hw).1 hne
      · intro v hv
        have hvm := Finset.mem_filter.mp hv
        have hmem := hcover v hvm.1
        simp only [List.flatten_cons, List.mem_append] at hmem
        exact hmem.resolve_left hvm.2
    have hsum : inside.card + outside.card = vertices.card :=
      Finset.card_filter_add_card_filter_not _
    simp only [List.length_cons]
    omega

def coloringCheck (adj : ℕ → ℕ) (mask bound : ℕ) (classes : List (List ℕ)) : Bool :=
  decide (classes.length ≤ bound) &&
    (decide (mask &&& maskOf classes.flatten = mask) &&
      classes.all (independentCheck adj))

theorem coloringCheck_sound {adj : ℕ → ℕ} {mask bound : ℕ}
    {classes : List (List ℕ)} (hcheck : coloringCheck adj mask bound classes = true)
    (vertices : Finset ℕ) (hmask : InMask mask vertices) (hclique : Clique adj vertices) :
    vertices.card ≤ bound := by
  obtain ⟨hsize, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hcover, hclasses⟩ := Bool.and_eq_true_iff.mp hrest
  have hsize' : classes.length ≤ bound := of_decide_eq_true hsize
  have hcover' : mask &&& maskOf classes.flatten = mask := of_decide_eq_true hcover
  apply (coloring_bound adj classes (List.all_eq_true.mp hclasses) vertices hclique ?_).trans hsize'
  intro v hv
  apply (testBit_maskOf classes.flatten v).mp
  have hbit := congrArg (fun n => n.testBit v) hcover'
  simpa only [Nat.testBit_and, hmask v hv, Bool.true_and] using hbit

inductive Certificate where
  | color (classes : List (List ℕ))
  | split (vertex : ℕ) (inside outside : Certificate)

def check (adj : ℕ → ℕ) (mask bound : ℕ) : Certificate → Bool
  | .color classes => coloringCheck adj mask bound classes
  | .split v inside outside =>
    match bound with
    | 0 => false
    | k + 1 => check adj (mask &&& adj v) k inside &&
        check adj (mask ^^^ 2 ^ v) (k + 1) outside

theorem check_sound (adj : ℕ → ℕ) (certificate : Certificate)
    (mask bound : ℕ) (hcheck : check adj mask bound certificate = true)
    (vertices : Finset ℕ) (hmask : InMask mask vertices) (hclique : Clique adj vertices) :
    vertices.card ≤ bound := by
  induction certificate generalizing mask bound vertices with
  | color classes => exact coloringCheck_sound hcheck vertices hmask hclique
  | split v inside outside ihin ihout =>
    cases bound with
    | zero => simp [check] at hcheck
    | succ k =>
      obtain ⟨hin, hout⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases hv : v ∈ vertices
      · have herase : (vertices.erase v).card ≤ k := by
          apply ihin (mask &&& adj v) k hin
          · intro w hw
            have hwm := Finset.mem_erase.mp hw
            simp only [Nat.testBit_and, hmask w hwm.2, Bool.true_and]
            exact hclique v hv w hwm.2 (Ne.symm hwm.1)
          · intro a ha b hb hne
            exact hclique a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hne
        have hcard := Finset.card_erase_add_one hv
        omega
      · apply ihout (mask ^^^ 2 ^ v) (k + 1) hout vertices ?_ hclique
        intro w hw
        have hne : v ≠ w := by intro heq; exact hv (heq ▸ hw)
        simp only [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hne,
          hmask w hw, Bool.bne_false]



end SensitivityCliqueCertificate


