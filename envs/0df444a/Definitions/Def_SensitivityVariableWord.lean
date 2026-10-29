-- Prove2me | Definitions.Def_SensitivityVariableWord
-- name    : SensitivityVariableWord
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-28T23:47:44.960708+00:00
-- url     : https://prove2.me/theorems/1a0f2c01-d616-4449-b679-77a45b8e1182
-- title:
--   Canonical recipe words with variable graph and labeling parameters
-- statement:
--   A graph datum consists of exactly the tournament, binary labeling, and cutoff data required by the recursive-profile certificate interface. Its vertex count $K>1$, regular outdegree, ordinary and source cutoffs, and finite list of defect cutoffs are variable. The datum includes proofs of all the original coherence, defect, and source bounds; none is weakened.
--
--   For a positive number of states, start with two matrices equal to one on and above the diagonal and zero below it. Given a recipe, apply the original zero and one transfer formulas using the datum's parameters. Replace each resulting entry on $[i,j]$ by the minimum over nonempty subintervals of $[i,j]$. A finite word specifies these stages in order, so its intermediate profiles are determined.
--
--   A word is admissible if every recipe satisfies the original validity predicate and every positive tolerance on an ordinary state lies below the datum's tolerance count. If $L$ is its length and $H$ is its terminal height, clamped below by two, the crossing predicate is
--
--   $$L>0,\qquad \text{the word is admissible},\qquad H^{43}<K^{20L}.$$
--
--   The file defines this interface and its periodic-orbit counterpart. It asserts neither that a crossing word exists nor that any fixed graph parameters suffice.
-- source:
--   Original parameter-free canonical-word reduction of SensitivityProfileCycle.Certificate and exists_215_certificate, https://prove2.me/theorems/6c031b2d-eb14-46d2-8d9e-f2db70527660. GraphData copies exactly the graph, labeling, and cutoff fields of https://prove2.me/definitions/6f70ee20-3318-4365-9377-022df0d68b3f. The step uses that module's rawZeroSourceCombined and rawOne without specializing any parameter. The interval envelope, unitProfile, and height come from SensitivityProfileSearch and SensitivityProfileWord; the fixed-parameter normalization theorem is https://prove2.me/theorems/ce0348ca-6a7e-4ada-a2fa-153d9cf45aa3. Underlying recursive bounds: accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and earlier community attribution. No source is claimed to supply a witness reaching 2.15.

import Definitions.Def_SensitivityProfileWord

/-!
Canonical finite words for arbitrary tournament and labeling parameters.
The numerical recurrence is exactly that of SensitivityProfileCycle.
No existence assertion or fixed tournament size is built into this interface.
-/

set_option autoImplicit false
namespace SensitivityVariableWord
open SensitivityProfileCycle SensitivityProfileSearch
open scoped Classical

structure GraphData where
  vertices : ℕ
  vertices_gt_one : 1 < vertices
  degree : ℕ
  ordinaryCutoff : ℕ
  ordinary_ge_four : 4 ≤ ordinaryCutoff
  sourceCutoff : ℕ
  source_ge_four : 4 ≤ sourceCutoff
  toleranceCount : ℕ
  cutoffs : Fin toleranceCount → ℕ
  cutoff_zero : extendCutoffs cutoffs 0 = ordinaryCutoff
  adj : Fin vertices → Fin vertices → Prop
  loopless : ∀ i, ¬ adj i i
  complement : ∀ {i j}, i ≠ j → (adj i j ↔ ¬ adj j i)
  outdegree : ∀ i, (Finset.univ.filter (adj i)).card = degree
  label : Fin vertices → Fin vertices → Fin 2
  coherent : ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
    (∀ i ∈ I, ∀ j ∈ I, adj i j → label i j = colors j) →
      I.card < ordinaryCutoff
  defect : ∀ q : Fin toleranceCount,
    ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
      (∀ i ∈ I, (I.filter (fun j => adj i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < cutoffs q
  source : ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
    (∃ s ∈ I, ∀ j ∈ I, j ≠ s → adj s j) →
    (∀ i ∈ I, (I.filter (fun j => adj i j ∧ label i j ≠ colors j)).card ≤ 0) →
      I.card < sourceCutoff

def GraphData.ofCertificate (c : Certificate) : GraphData where
  vertices := c.vertices
  vertices_gt_one := c.vertices_gt_one
  degree := c.degree
  ordinaryCutoff := c.ordinaryCutoff
  ordinary_ge_four := c.ordinary_ge_four
  sourceCutoff := c.sourceCutoff
  source_ge_four := c.source_ge_four
  toleranceCount := c.toleranceCount
  cutoffs := c.cutoffs
  cutoff_zero := c.cutoff_zero
  adj := c.adj
  loopless := c.loopless
  complement := c.complement
  outdegree := c.outdegree
  label := c.label
  coherent := c.coherent
  defect := c.defect
  source := c.source

abbrev unitProfile := SensitivityProfileWord.unitProfile
abbrev height {n : ℕ} := @SensitivityProfileWord.height n

def step {n : ℕ} (G : GraphData) (C : Recipe n) (P : Profile n) : Profile n :=
  ⟨envelope (rawZeroSourceCombined G.vertices G.ordinaryCutoff
      (extendCutoffs G.cutoffs) G.sourceCutoff C P.zero P.one),
    envelope (rawOne G.degree C P.zero P.one)⟩

def run {n : ℕ} (G : GraphData) (word : List (Recipe n)) (P : Profile n) : Profile n :=
  word.foldl (fun Q C => step G C Q) (normalize P)

def Admissible {n : ℕ} (G : GraphData) (word : List (Recipe n)) : Prop :=
  ∀ C ∈ word, C.Valid ∧ ∀ i, 3 ≤ i.val → 0 < C.tol i → C.tol i < G.toleranceCount

def Crosses215 {n : ℕ} (G : GraphData) (word : List (Recipe n)) : Prop :=
  word ≠ [] ∧ Admissible G word ∧
    height (run G word (unitProfile n)) ^ 43 < G.vertices ^ (20 * word.length)

def orbit {n p : ℕ} (G : GraphData) (recipes : Fin (p+1) → Recipe n)
    (initial : Profile n) : ℕ → Profile n
  | 0 => normalize initial
  | d+1 => step G (periodicRecipe recipes d) (orbit G recipes initial d)

def ReturnsWithin {n p : ℕ} (G : GraphData) (recipes : Fin (p+1) → Recipe n)
    (initial : Profile n) (radius : ℕ) : Prop :=
  ∀ i j, i ≤ j →
    (orbit G recipes initial (p+1)).zero i j ≤
      (normalize initial).zero i j * radius ∧
    (orbit G recipes initial (p+1)).one i j ≤
      (normalize initial).one i j * radius

end SensitivityVariableWord


