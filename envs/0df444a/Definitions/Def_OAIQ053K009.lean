-- Prove2me | Definitions.Def_OAIQ053K009
-- name    : OAIQ053K009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:13.816894+00:00
-- url     : https://prove2.me/theorems/ac1f8ca6-943c-4faa-bb51-4ca51e738db9
-- title:
--   Definitions bundle OAIQ053K009 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 49 definitions, 3 inductive types or structures, 1 instance and 44 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Amplifier.capLoss`, `OAI.MetricKMedian.PCP.Amplifier.loss`, `OAI.MetricKMedian.PCP.Amplifier.nodeCoeff`, `OAI.MetricKMedian.PCP.Amplifier.radius`, `OAI.MetricKMedian.PCP.Amplifier.steps`, `OAI.MetricKMedian.PCP.BiProjection`, `OAI.MetricKMedian.PCP.BiProjection.CollisionBound`, `OAI.MetricKMedian.PCP.BiProjection.Consistent`, `OAI.MetricKMedian.PCP.BiProjection.average`, `OAI.MetricKMedian.PCP.BiProjection.collision`, `OAI.MetricKMedian.PCP.BiProjection.prod`, `OAI.MetricKMedian.PCP.BiProjection.push`, `OAI.MetricKMedian.PCP.BiProjection.source`, `OAI.MetricKMedian.PCP.CloudCopies.Dart`, `OAI.MetricKMedian.PCP.ExpanderFamily.Branch`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree`, `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort`, `OAI.MetricKMedian.PCP.ExpanderFamily.Vertex`, `OAI.MetricKMedian.PCP.ExpanderFamily.growth`, `OAI.MetricKMedian.PCP.ExpanderFamily.level`, `OAI.MetricKMedian.PCP.MixedNorm.sq`, `OAI.MetricKMedian.PCP.PortGraph`, `OAI.MetricKMedian.PCP.PortGraph.BlendPort`, `OAI.MetricKMedian.PCP.PortGraph.Walk`, `OAI.MetricKMedian.PCP.PortGraph.Walk.catPort`, `OAI.MetricKMedian.PCP.PortGraph.Walk.catVertex`, `OAI.MetricKMedian.PCP.PortGraph.Walk.ofWord`, `OAI.MetricKMedian.PCP.PortGraph.Walk.reverse`, `OAI.MetricKMedian.PCP.PortGraph.Walk.reverseEquiv`, `OAI.MetricKMedian.PCP.PortGraph.Walk.segment`, `OAI.MetricKMedian.PCP.PortGraph.Walk.wordEquiv`, `OAI.MetricKMedian.PCP.PortGraph.adjacency`, `OAI.MetricKMedian.PCP.PortGraph.back`, `OAI.MetricKMedian.PCP.PortGraph.badCount`, `OAI.MetricKMedian.PCP.PortGraph.blend`, `OAI.MetricKMedian.PCP.PortGraph.blendRotate`, `OAI.MetricKMedian.PCP.PortGraph.countMean`, `OAI.MetricKMedian.PCP.PortGraph.edgeHit`, `OAI.MetricKMedian.PCP.PortGraph.portEmbed`, `OAI.MetricKMedian.PCP.PortGraph.propagate` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_Amplifier`, `KMedian_Amplification_AmplifierSize`, `KMedian_Expanders_CloudCopies`, `KMedian_Expanders_ExpanderFamily`, `KMedian_Expanders_GraphExtend`, `KMedian_Expanders_GraphMix`, `KMedian_Expanders_GraphProducts`, `KMedian_Expanders_GraphRelabel`, `KMedian_Expanders_PortWalk`, `KMedian_Expanders_Rademacher`, `KMedian_Expanders_SpectralWalk`, `KMedian_Expanders_Stopped`, `KMedian_Expanders_WalkMoments`, `KMedian_Expanders_WalkSegments`, `KMedian_Projection_Bound`, `KMedian_Projection_Norm`, `KMedian_Projection_Operator`, `KMedian_Projection_Product`, `KMedian_Projection_Repeat`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K023`, `OAIQ053K024`, `OAIQ053K025` and `OAIQ053K026`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_PortWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPortWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

structure PortGraph (V D : Type) where
  rotate : V × D ≃ V × D
  involutive : Function.Involutive rotate

namespace PortGraph
variable {V D : Type} (G : PortGraph V D)
def step (v : V) (d : D) : V := (G.rotate (v,d)).1
def back (v : V) (d : D) : D := (G.rotate (v,d)).2

@[simp] theorem rotate_step_back (v : V) (d : D) :
    G.rotate (G.step v d, G.back v d) = (v,d) := G.involutive (v,d)
@[simp] theorem step_back (v : V) (d : D) :
    G.step (G.step v d) (G.back v d) = v := congrArg Prod.fst (G.rotate_step_back v d)
@[simp] theorem back_back (v : V) (d : D) :
    G.back (G.step v d) (G.back v d) = d := congrArg Prod.snd (G.rotate_step_back v d)

def trace : (n : ℕ) → V → (Fin n → D) → Fin (n+1) → V
  | 0, v, _ => fun _ => v
  | n+1, v, c => Fin.cases v (trace n (G.step v (c 0)) (fun i => c i.succ))

@[simp] theorem trace_zero (n : ℕ) (v : V) (c : Fin n → D) : G.trace n v c 0 = v := by
  cases n <;> rfl

@[simp] theorem trace_succ (n : ℕ) (v : V) (c : Fin (n+1) → D) (i : Fin (n+1)) :
    G.trace (n+1) v c i.succ = G.trace n (G.step v (c 0)) (fun j => c j.succ) i := rfl

theorem trace_chain (n : ℕ) (v : V) (c : Fin n → D) (i : Fin n) :
    G.step (G.trace n v c i.castSucc) (c i) = G.trace n v c i.succ := by
  induction n generalizing v with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change G.step v (c 0) = G.trace n (G.step v (c 0)) (fun k => c k.succ) 0
      exact (G.trace_zero n _ _).symm
    · simpa only [Fin.castSucc_succ, trace_succ] using
        ih (G.step v (c 0)) (fun k => c k.succ) j

structure Walk (n : ℕ) where
  vertex : Fin (n+1) → V
  port : Fin n → D
  chain : ∀ i, G.step (vertex i.castSucc) (port i) = vertex i.succ

namespace Walk
variable {G} {n : ℕ}
@[ext] theorem ext {p q : G.Walk n} (hv : p.vertex = q.vertex) (hp : p.port = q.port) : p = q := by
  cases p; cases q; cases hv; cases hp; rfl

theorem vertex_eq_trace (p : G.Walk n) :
    p.vertex = G.trace n (p.vertex 0) p.port := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    rw [← p.chain i, ← G.trace_chain n (p.vertex 0) p.port i, hi]

def ofWord (v : V) (c : Fin n → D) : G.Walk n :=
  ⟨G.trace n v c, c, G.trace_chain n v c⟩

def wordEquiv : G.Walk n ≃ V × (Fin n → D) where
  toFun p := (p.vertex 0, p.port)
  invFun p := ofWord p.1 p.2
  left_inv p := by
    apply Walk.ext
    · exact p.vertex_eq_trace.symm
    · rfl
  right_inv p := by simp [ofWord]

def reverse (p : G.Walk n) : G.Walk n where
  vertex i := p.vertex i.rev
  port i := G.back (p.vertex i.rev.castSucc) (p.port i.rev)
  chain i := by
    have h := p.chain i.rev
    rw [Fin.rev_castSucc, Fin.rev_succ]
    rw [← h]
    exact G.step_back _ _

@[simp] theorem reverse_reverse (p : G.Walk n) : p.reverse.reverse = p := by
  apply Walk.ext
  · funext i
    simp [reverse]
  · funext i
    simp only [reverse, Fin.rev_rev, Fin.rev_castSucc]
    rw [← p.chain i]
    exact G.back_back _ _

def reverseEquiv : G.Walk n ≃ G.Walk n :=
  ⟨reverse,reverse,reverse_reverse,reverse_reverse⟩

@[simp] theorem reverse_start (p : G.Walk n) : p.reverse.vertex 0 = p.vertex (Fin.last n) := by
  simp [reverse]

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPortWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkSegments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalkSegments

namespace MetricKMedian.PCP.PortGraph
open Finset
open scoped BigOperators

variable {V D : Type} {G : PortGraph V D}
namespace Walk
variable {n m : ℕ}

def segment (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) : G.Walk l where
  vertex i := p.vertex ⟨a+i.val, by omega⟩
  port i := p.port ⟨a+i.val, by omega⟩
  chain i := p.chain ⟨a+i.val, by omega⟩

@[simp] theorem segment_vertex (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) (i : Fin (l+1)) :
    (p.segment a l h).vertex i = p.vertex ⟨a+i.val, by omega⟩ := rfl
@[simp] theorem segment_port (p : G.Walk n) (a l : ℕ) (h : a+l ≤ n) (i : Fin l) :
    (p.segment a l h).port i = p.port ⟨a+i.val, by omega⟩ := rfl

def catVertex (p : G.Walk n) (q : G.Walk m) (i : Fin (n+m+1)) : V :=
  if h : i.val ≤ n then p.vertex ⟨i.val,by omega⟩
  else q.vertex ⟨i.val-n,by omega⟩
def catPort (p : G.Walk n) (q : G.Walk m) (i : Fin (n+m)) : D :=
  if h : i.val < n then p.port ⟨i.val,h⟩
  else q.port ⟨i.val-n,by omega⟩

end Walk
end MetricKMedian.PCP.PortGraph

end Inline_PCPWalkSegments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

theorem expect_prod (f : S × T → ℝ) :
    (𝔼 p, f p) = 𝔼 s, 𝔼 t, f (s,t) := by
  rw [← univ_product_univ, expect_product]

noncomputable def pairing (f g : S → ℝ) : ℝ := 𝔼 s, f s * g s

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

noncomputable def adjacency (f : V → ℝ) (v : V) : ℝ := 𝔼 d, f (G.step v d)

noncomputable def propagate : ℕ → (V → ℝ) → V → ℝ
  | 0, f => f
  | n+1, f => G.adjacency (propagate n f)

omit [Fintype V] [Nonempty D] in
@[simp] theorem propagate_zero (f : V → ℝ) : G.propagate 0 f = f := rfl
omit [Fintype V] [Nonempty D] in
@[simp] theorem propagate_succ (n : ℕ) (f : V → ℝ) :
    G.propagate (n+1) f = G.adjacency (G.propagate n f) := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_WalkMoments
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalkMoments

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {D : Type} [Fintype D]

theorem expect_word_succ (n : ℕ) (f : (Fin (n+1) → D) → ℝ) :
    (𝔼 c, f c) = 𝔼 d : D, 𝔼 c : Fin n → D, f (Fin.cons d c) := by
  have h := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => D))
    (fun p : D × (Fin n → D) => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [← h, expect_prod]

namespace PortGraph
variable {V : Type} [Fintype V] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D) (bad : V × D → Prop)

noncomputable def edgeHit (_G : PortGraph V D) (v : V) (d : D) : ℝ := by
  classical
  exact if bad (v,d) then 1 else 0

noncomputable def badCount : (n : ℕ) → V → (Fin n → D) → ℝ
  | 0, _, _ => 0
  | n+1, v, c => G.edgeHit bad v (c 0) + badCount n (G.step v (c 0)) (fun i => c i.succ)

noncomputable def countMean (n : ℕ) (v : V) : ℝ := 𝔼 c, G.badCount bad n v c

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem edgeHit_sq (v : V) (d : D) : G.edgeHit bad v d ^ 2 = G.edgeHit bad v d := by
  classical
  unfold edgeHit
  split_ifs <;> norm_num

omit [Fintype D] [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem badCount_cons (n : ℕ) (v : V) (d : D) (c : Fin n → D) :
    G.badCount bad (n+1) v (Fin.cons d c) = G.edgeHit bad v d + G.badCount bad n (G.step v d) c := by
  simp only [badCount, Fin.cons_zero, Fin.cons_succ]

omit [Fintype V] [Nonempty V] [Nonempty D] in
@[simp] theorem countMean_zero : G.countMean bad 0 = fun _ => 0 := by
  funext v
  simp [countMean,badCount]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPWalkMoments

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Stopped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPStopped

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
variable (t : ℕ)
def length : (n : ℕ) → (Fin n → Fin (t+1)) → ℕ
  | 0, _ => 0
  | n+1, c => if c 0 = 0 then 0 else 1 + length n (fun i => c i.succ)

theorem length_le (n : ℕ) (c : Fin n → Fin (t+1)) : length t n c ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold length
    split_ifs
    · omega
    · have := ih (fun i => c i.succ); omega

@[simp] theorem length_cons (n : ℕ) (d : Fin (t+1)) (c : Fin n → Fin (t+1)) :
    length t (n+1) (Fin.cons d c) = if d=0 then 0 else 1+length t n c := by
  simp [length]

end Stopped

end MetricKMedian.PCP

end Inline_PCPStopped

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma extend_involutive {U W : Type} [Fintype U] [DecidableEq W]
    (p : U ≃ U) (hp : Function.Involutive p) (e : U ↪ W) :
    Function.Involutive (Equiv.Perm.viaFintypeEmbedding p e) := by
  intro w
  by_cases h : w ∈ Set.range e
  · obtain ⟨u,rfl⟩ := h
    simp only [Equiv.Perm.viaFintypeEmbedding_apply_image]
    exact congrArg e (hp u)
  · rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ h,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ h]

namespace PortGraph
variable {V W D : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
variable (G : PortGraph V D) (e : V ↪ W)

def portEmbed : V × D ↪ W × D := e.prodMap (Function.Embedding.refl D)

omit [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D] in
lemma portEmbed_range (p : W × D) : p ∈ Set.range (portEmbed e) ↔ p.1 ∈ Set.range e := by
  constructor
  · rintro ⟨⟨v,d⟩,h⟩
    exact ⟨v,congrArg Prod.fst h⟩
  · rintro ⟨v,h⟩
    exact ⟨(v,p.2),Prod.ext h rfl⟩

end PortGraph

end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphMix
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}
variable (G : PortGraph V D) (H : PortGraph V S)
abbrev BlendPort := Fin 3 × (D × S)

def blendRotate (p : V × BlendPort (D := D) (S := S)) : V × BlendPort (D := D) (S := S) :=
  if p.2.1=0 then
    (G.step p.1 p.2.2.1,(p.2.1,(G.back p.1 p.2.2.1,p.2.2.2))) else
    (H.step p.1 p.2.2.2,(p.2.1,(p.2.2.1,H.back p.1 p.2.2.2)))

lemma blendRotate_involutive : Function.Involutive (blendRotate G H) := by
  rintro ⟨v,i,d,s⟩
  by_cases hi : i=0 <;> simp [blendRotate,hi,step_back,back_back]

def blend : PortGraph V (BlendPort (D := D) (S := S)) where
  rotate := { toFun := blendRotate G H
              invFun := blendRotate G H
              left_inv := blendRotate_involutive G H
              right_inv := blendRotate_involutive G H }
  involutive := blendRotate_involutive G H

@[simp] lemma blend_step (v : V) (i : Fin 3) (d : D) (s : S) :
    (G.blend H).step v (i,d,s)=if i=0 then G.step v d else H.step v s := by
  change (blendRotate G H (v,i,d,s)).1 = _
  by_cases h : i=0 <;> simp [blendRotate,h]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphRelabel
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphRelabel

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D W E : Type}

def relabel (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) : PortGraph W E where
  rotate := ((Equiv.prodCongr e d).symm.trans G.rotate).trans (Equiv.prodCongr e d)
  involutive p := by
    change (Equiv.prodCongr e d) (G.rotate ((Equiv.prodCongr e d).symm
      ((Equiv.prodCongr e d) (G.rotate ((Equiv.prodCongr e d).symm p)))))=p
    rw [Equiv.symm_apply_apply,G.involutive,Equiv.apply_symm_apply]

@[simp] lemma relabel_step (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) (v : W) (s : E) :
    (G.relabel e d).step v s=e (G.step (e.symm v) (d.symm s)) := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphRelabel

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Rademacher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRademacher

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Rademacher
variable {S : Type} [Fintype S] [Nonempty S] (f : S → ℝ)
variable (hf : ∀ x, f x = 1 ∨ f x = -1) (hmean : (𝔼 x, f x)=0)

include hf hmean in
lemma expect_apply (H : ℝ → ℝ) : (𝔼 x, H (f x)) = (H 1 + H (-1))/2 := by
  have he (x : S) : H (f x) = (1+f x)/2*H 1+(1-f x)/2*H (-1) := by
    rcases hf x with h | h <;> rw [h] <;> ring
  simp_rw [he]
  rw [expect_add_distrib, ← expect_mul, ← expect_mul, ← Finset.expect_div,
    ← Finset.expect_div, expect_add_distrib, expect_sub_distrib, hmean]
  simp only [Fintype.expect_const]
  ring

def wordSum (n : ℕ) (c : Fin n → S) : ℝ := ∑ i, f (c i)
noncomputable def moment (n k : ℕ) : ℝ := 𝔼 c : Fin n → S, wordSum f n c ^ k

omit [Fintype S] [Nonempty S] in
lemma wordSum_cons (n : ℕ) (x : S) (c : Fin n → S) :
    wordSum f (n+1) (Fin.cons x c) = f x + wordSum f n c := by
  simp [wordSum, Fin.sum_univ_succ]

include hf hmean

lemma moment_succ (n k : ℕ) : moment f (n+1) k =
    𝔼 c : Fin n → S, ((wordSum f n c+1)^k+(wordSum f n c-1)^k)/2 := by
  unfold moment
  rw [expect_word_succ, expect_comm]
  apply expect_congr rfl
  intro c _
  simp_rw [wordSum_cons, add_comm (f _) (wordSum f n c)]
  simpa only [sub_eq_add_neg] using expect_apply f hf hmean (fun z => (wordSum f n c+z)^k)

lemma moment2_succ (n : ℕ) : moment f (n+1) 2 = moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^2+(s-1)^2)/2=s^2+1 := by ring
  simp_rw [he]
  rw [expect_add_distrib, Fintype.expect_const]
  rfl

lemma moment4_succ (n : ℕ) : moment f (n+1) 4 = moment f n 4 + 6*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^4+(s-1)^4)/2=s^4+6*s^2+1 := by ring
  simp_rw [he]
  rw [expect_add_distrib, expect_add_distrib, ← mul_expect, Fintype.expect_const]
  rfl

lemma moment6_succ (n : ℕ) : moment f (n+1) 6 =
    moment f n 6 + 15*moment f n 4 + 15*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^6+(s-1)^6)/2=s^6+15*s^4+15*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

lemma moment8_succ (n : ℕ) : moment f (n+1) 8 =
    moment f n 8 + 28*moment f n 6 + 70*moment f n 4 + 28*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^8+(s-1)^8)/2=s^8+28*s^6+70*s^4+28*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

lemma moment10_succ (n : ℕ) : moment f (n+1) 10 =
    moment f n 10 + 45*moment f n 8 + 210*moment f n 6 + 210*moment f n 4 +
      45*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^10+(s-1)^10)/2=
      s^10+45*s^8+210*s^6+210*s^4+45*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

theorem moments_bound (n : ℕ) :
    moment f n 2 ≤ n ∧ moment f n 4 ≤ 3*(n:ℝ)^2 ∧
    moment f n 6 ≤ 15*(n:ℝ)^3 ∧ moment f n 8 ≤ 105*(n:ℝ)^4 ∧
    moment f n 10 ≤ 945*(n:ℝ)^5 := by
  induction n with
  | zero => simp [moment,wordSum]
  | succ n ih =>
    rcases ih with ⟨h2,h4,h6,h8,h10⟩
    rw [moment2_succ f hf hmean, moment4_succ f hf hmean,
      moment6_succ f hf hmean, moment8_succ f hf hmean, moment10_succ f hf hmean]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hn2 : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
    have hn3 : (0:ℝ) ≤ (n:ℝ)^3 := pow_nonneg hn _
    constructor
    · linarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith

end Rademacher
end MetricKMedian.PCP

end Inline_PCPRademacher

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphProducts
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphProducts

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}

def squareRotate (G : PortGraph V D) (p : V × (D × D)) : V × (D × D) :=
  (G.step (G.step p.1 p.2.1) p.2.2,
   (G.back (G.step p.1 p.2.1) p.2.2,G.back p.1 p.2.1))

lemma squareRotate_involutive (G : PortGraph V D) : Function.Involutive (squareRotate G) := by
  rintro ⟨v,d,e⟩
  simp only [squareRotate,step_back,back_back]

def square (G : PortGraph V D) : PortGraph V (D × D) where
  rotate := { toFun := squareRotate G
              invFun := squareRotate G
              left_inv := squareRotate_involutive G
              right_inv := squareRotate_involutive G }
  involutive := squareRotate_involutive G

@[simp] lemma square_step (G : PortGraph V D) (v : V) (de : D × D) :
    G.square.step v de=G.step (G.step v de.1) de.2 := rfl

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

def zigzagRotate (G : PortGraph V D) (H : PortGraph D S)
    (p : (V × D) × (S × S)) : (V × D) × (S × S) :=
  ((G.step p.1.1 (H.step p.1.2 p.2.1),
    H.step (G.back p.1.1 (H.step p.1.2 p.2.1)) p.2.2),
   (H.back (G.back p.1.1 (H.step p.1.2 p.2.1)) p.2.2,H.back p.1.2 p.2.1))

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

lemma zigzagRotate_involutive (G : PortGraph V D) (H : PortGraph D S) :
    Function.Involutive (zigzagRotate G H) := by
  rintro ⟨⟨v,d⟩,s,t⟩
  simp only [zigzagRotate,step_back,back_back]

def zigzag (G : PortGraph V D) (H : PortGraph D S) : PortGraph (V × D) (S × S) where
  rotate := { toFun := zigzagRotate G H
              invFun := zigzagRotate G H
              left_inv := zigzagRotate_involutive G H
              right_inv := zigzagRotate_involutive G H }
  involutive := zigzagRotate_involutive G H

@[simp] lemma zigzag_step (G : PortGraph V D) (H : PortGraph D S) (v : V × D) (s : S × S) :
    (G.zigzag H).step v s=(G.step v.1 (H.step v.2 s.1),
      H.step (G.back v.1 (H.step v.2 s.1)) s.2) := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphProducts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

abbrev SmallPort := Fin (2^44)
abbrev Degree := SmallPort × SmallPort
abbrev Branch := Degree × Degree

def growth : ℕ := (2^44)^4

lemma growth_gt_one : 1 < growth := by norm_num [growth]

def Vertex : ℕ → Type
  | 0 => Unit
  | n+1 => Vertex n × Branch

instance vertexFintype : (n : ℕ) → Fintype (Vertex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := vertexFintype n; inferInstanceAs (Fintype (Vertex n × Branch))

lemma card_branch : Fintype.card Branch=growth := by
  simp only [Fintype.card_prod,Fintype.card_fin,growth]
  ring

lemma card_vertex (n : ℕ) : Fintype.card (Vertex n)=growth^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × Branch)=growth^(n+1)
    rw [Fintype.card_prod,ih,card_branch,pow_succ]

def level (n : ℕ) : ℕ := Nat.log growth (n+1)+1

lemma padding_lower (n : ℕ) : n+1 ≤ Fintype.card (Vertex (level n)) := by
  rw [card_vertex]
  exact Nat.le_of_lt (Nat.lt_pow_succ_log_self growth_gt_one (n+1))

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudCopies

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype V] [Fintype E]
abbrev Dart := E × Bool

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPCloudCopies

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Amplifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
def loss : ℕ := 18*ExpanderFamily.growth^2
def capLoss : ℕ := 384*576*16^4
def steps : ℕ := 2*capLoss*loss
def radius : ℕ := 2*steps+2

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifier

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierSize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
@[irreducible] noncomputable def nodeCoeff : ℕ := 2*ExpanderFamily.growth^2
end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifierSize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionNorm

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {V T : Type} [Fintype V] [Fintype T]

noncomputable def sq (f : V → T → ℝ) : ℝ := 𝔼 v, ∑ t, f v t ^ 2

end MixedNorm
end MetricKMedian.PCP

end Inline_PCPProjectionNorm

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

structure BiProjection (U V D S A B : Type) where
  edge : U × D ≃ V × S
  project : U × D → A → B

namespace ProjectionMass
variable {A B : Type} [Fintype A] [Fintype B]
noncomputable def push (π : A → B) (f : A → ℝ) (b : B) : ℝ := ∑ a, if π a=b then f a else 0

end ProjectionMass

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

def source (v : V) (s : S) : U × D := G.edge.symm (v,s)
noncomputable def average (h : U → ℝ) (v : V) := 𝔼 s, h (G.source v s).1
noncomputable def push (f : U → A → T → ℝ) (v : V) (b : B) (t : T) : ℝ :=
  𝔼 s, ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b
noncomputable def collision (f : U → A → T → ℝ) : ℝ :=
  MixedNorm.sq (fun v (p : B × T) => G.push f v p.1 p.2)

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

def CollisionBound (r : ℝ) : Prop := ∀ (T : Type) [Fintype T]
  (f : U → A → T → ℝ), (∀ u a t, 0 ≤ f u a t) → ∀ M : ℝ, 0 ≤ M →
  (∀ u, ∑ t, (∑ a, f u a t)^2≤M) → G.collision f ≤ r*M

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProduct

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T I : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T] [Fintype I]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

def prod : BiProjection (U × U') (V × V') (D × D') (S × S') (A × A') (B × B') where
  edge := {
    toFun p := (((G.edge (p.1.1,p.2.1)).1,(H.edge (p.1.2,p.2.2)).1),
      ((G.edge (p.1.1,p.2.1)).2,(H.edge (p.1.2,p.2.2)).2))
    invFun p := (((G.edge.symm (p.1.1,p.2.1)).1,(H.edge.symm (p.1.2,p.2.2)).1),
      ((G.edge.symm (p.1.1,p.2.1)).2,(H.edge.symm (p.1.2,p.2.2)).2))
    left_inv p := by simp
    right_inv p := by simp }
  project p a := (G.project (p.1.1,p.2.1) a.1,H.project (p.1.2,p.2.2) a.2)

omit [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
@[simp] lemma prod_source (v : V × V') (s : S × S') :
    (G.prod H).source v s = (((G.source v.1 s.1).1,(H.source v.2 s.2).1),
      ((G.source v.1 s.1).2,(H.source v.2 s.2).2)) := rfl

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionProduct

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Repeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepeat

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)
def Consistent (G : BiProjection U V D S A B) : Prop :=
  ∀ u d e, (G.edge (u,d)).1=(G.edge (u,e)).1 → ∀ a, G.project (u,d) a=G.project (u,e) a

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
end


