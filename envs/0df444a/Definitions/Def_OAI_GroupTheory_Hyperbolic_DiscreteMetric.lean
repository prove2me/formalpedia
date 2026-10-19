-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
-- name    : OAI_GroupTheory_Hyperbolic_DiscreteMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:13:57.01056+00:00
-- url     : https://prove2.me/theorems/577d1134-1558-4b14-885e-628025c7d7ea
-- title:
--   Integer-valued metrics, discrete paths and thin triangles
-- statement:
--   Elementary coarse geometry for metrics with values in $\mathbb N$.
--
--   1. **Metrics and paths.** A discrete metric is a symmetric function $d:V\times V\to\mathbb N$ with $d(x,x)=0$ and the triangle inequality. A path from $a$ to $b$ has a length $n$ and points $p_0=a,\ p_1,\dots$, eventually constant equal to $b$ from index $n$, with $d(p_i,p_{i+1})\le1$ for $i<n$. It is geodesic if $n=d(a,b)$, and $x$ lies on it if $x=p_i$ for some $i\le n$.
--   2. **Operations.** Paths have constant paths, concatenation, reversal and subpaths. The integral of $F:V\times V\to\mathbb Z$ along a path is $\sum_{i<n}F(p_i,p_{i+1})$.
--   3. **Tent forms.** For points $o,a$ and a radius $R$, the tent is $\tau(x)=\max(0,R-d(o,x))$ and the form is
--   $$
--   \omega(x,y)=\bigl(\tau(x)+\tau(y)\bigr)\bigl(d(a,y)-d(a,x)\bigr).
--   $$
--   The metric has cochain bound $B$ if every closed path $p$ has $|\int_p\omega|\le B\cdot\mathrm{length}(p)$ for all $o,a,R$.
--   4. **Thin triangles and bypasses.** A triangle of paths is $T$-near if every point of each side is within $T$ of one of the other two sides. A short bypass of size $K$ around $o$ at radius $T$ is a geodesic through $o$ from $a$ to $b$ together with a path from $b$ back to $a$ that stays at distance at least $T$ from $o$, the two lengths summing to at most $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075.Discrete

structure Metric (V : Type) where
  dist : V → V → ℕ
  self : ∀ x, dist x x = 0
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

variable {V : Type} (M : Metric V)

structure Path (a b : V) where
  length : ℕ
  point : ℕ → V
  zero : point 0 = a
  stable : ∀ i, length ≤ i → point i = b
  step : ∀ i, i < length → M.dist (point i) (point (i+1)) ≤ 1

namespace Path
variable {M} {a b c : V}

@[simp] theorem last (p : Path M a b) : p.point p.length = b := p.stable _ le_rfl

@[simp] theorem at_min (p : Path M a b) (i : ℕ) : p.point (min i p.length) = p.point i := by
  by_cases h : i ≤ p.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega),p.last,p.stable i (by omega)]

def Geodesic (p : Path M a b) : Prop := p.length = M.dist a b

def Mem (p : Path M a b) (x : V) : Prop := ∃ i ≤ p.length, p.point i = x

@[simp] theorem start_mem (p : Path M a b) : p.Mem a := ⟨0,Nat.zero_le _,p.zero⟩
@[simp] theorem end_mem (p : Path M a b) : p.Mem b := ⟨p.length,le_rfl,p.last⟩

def nil (a : V) : Path M a a where
  length := 0
  point _ := a
  zero := rfl
  stable _ _ := rfl
  step := by intro i hi; omega

def append (p : Path M a b) (q : Path M b c) : Path M a c where
  length := p.length + q.length
  point i := if i < p.length then p.point i else q.point (i-p.length)
  zero := by
    split_ifs with h
    · exact p.zero
    · simpa only [Nat.zero_sub,q.zero] using
        (p.stable 0 (by omega)).symm.trans p.zero
  stable i hi := by
    rw [ite_eq_right (by omega),q.stable _ (by omega)]
  step i hi := by
    by_cases h : i+1 < p.length
    · simpa only [ite_eq_left h,ite_eq_left (show i < p.length by omega)] using p.step i (by omega)
    · by_cases h' : i < p.length
      · have he : i+1 = p.length := by omega
        simpa only [ite_eq_left h',ite_eq_right h,he,Nat.sub_self,q.zero,p.last,ite_self] using p.step i h'
      · simpa only [ite_eq_right h',ite_eq_right h,show i+1-p.length = (i-p.length)+1 by omega] using
          q.step (i-p.length) (by omega)

@[simp] theorem length_append (p : Path M a b) (q : Path M b c) :
    (p.append q).length = p.length+q.length := rfl

@[simp] theorem append_at_left (p : Path M a b) (q : Path M b c) {i : ℕ} (hi : i ≤ p.length) :
    (p.append q).point i = p.point i := by
  change (if i < p.length then _ else _) = _
  split_ifs with h
  · rfl
  · have he : i = p.length := by omega
    simp only [he,Nat.sub_self,q.zero,p.last]

@[simp] theorem append_at_right (p : Path M a b) (q : Path M b c) (i : ℕ) :
    (p.append q).point (p.length+i) = q.point i := by
  change (if p.length+i < p.length then _ else _) = _
  simp

def reverse (p : Path M a b) : Path M b a where
  length := p.length
  point i := p.point (p.length-i)
  zero := by simpa only [Nat.sub_zero] using p.last
  stable i hi := by simpa only [Nat.sub_eq_zero_of_le hi] using p.zero
  step i hi := by
    rw [M.symm]
    have he : p.length-i = (p.length-(i+1))+1 := by omega
    rw [he]
    exact p.step _ (by omega)

def sub (p : Path M a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    Path M (p.point i) (p.point j) where
  length := j-i
  point k := p.point (min (i+k) j)
  zero := by simp only [Nat.add_zero,min_eq_left hij]
  stable k hk := by rw [min_eq_right (by omega)]
  step k hk := by
    rw [min_eq_left (show i+k ≤ j by omega),min_eq_left (show i+(k+1) ≤ j by omega)]
    simpa only [Nat.add_assoc] using p.step (i+k) (by omega)

@[simp] theorem sub_at (p : Path M a b) {i j k : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    (hk : k ≤ j-i) : (p.sub i j hij hj).point k = p.point (i+k) := by
  change p.point (min (i+k) j) = _
  rw [min_eq_left (by omega)]

def integral (p : Path M a b) (F : V → V → ℤ) : ℤ :=
  ∑ i ∈ Finset.range p.length, F (p.point i) (p.point (i+1))

@[simp] theorem integral_nil (a : V) (F : V → V → ℤ) : (nil (M:=M) a).integral F = 0 := by
  simp [integral,nil]

end Path

namespace Metric
variable {M}

def tent (o : V) (R : ℕ) (x : V) : ℤ := max 0 ((R:ℤ)-M.dist o x)

def form (o a : V) (R : ℕ) (x y : V) : ℤ :=
  (M.tent o R x+M.tent o R y)*((M.dist a y:ℤ)-M.dist a x)

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

def SideNear (T : ℕ) (p : Path M a b) (q : Path M c d) (s : Path M e f) : Prop :=
  ∀ x, p.Mem x → ∃ y, (q.Mem y ∨ s.Mem y) ∧ M.dist x y ≤ T

def TriangleNear (T : ℕ) (p : Path M a b) (q : Path M b c) (s : Path M a c) : Prop :=
  SideNear T p q s ∧ SideNear T q s p ∧ SideNear T s p q

end Path

/-- A linear bound on the integral, for every clipped distance cochain. -/
def CochainBound (M : Metric V) (B : ℕ) : Prop :=
  ∀ (o a x : V) (T : ℕ) (p : Path M x x),
    |p.integral (M.form o a T)| ≤ (B:ℤ)*p.length

/-- A geodesic arc through `o`, closed by a short bypass outside the open T-ball. -/
def ShortBypass (M : Metric V) (T : ℕ) (o : V) (K : ℕ) : Prop :=
  ∃ (a b : V) (p : Path M a b) (q : Path M b a),
    p.Geodesic ∧ p.Mem o ∧ (∀ x, q.Mem x → T ≤ M.dist o x) ∧
      p.length+q.length ≤ K

end Release075.Discrete

end OAI


