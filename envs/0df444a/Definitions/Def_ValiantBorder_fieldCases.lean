-- Prove2me | Definitions.Def_ValiantBorder_fieldCases
-- name    : ValiantBorder_fieldCases
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:21:14.729672+00:00
-- url     : https://prove2.me/theorems/9083ee1f-5350-45c3-bbe8-c8216822ac29
-- title:
--   Flat and contracting fields in the tensor-price argument
-- statement:
--   A price measures pairwise distances through spectral points of tensors. A field is flat when every finite Euclidean configuration gives a price. It is contracting when, for some binary matrix dimension μ and some real s with 1 ≤ s and s² < μ, the root-mean-square price for full-rank displacements is at most s times the corresponding price for rank-one displacements.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Alternative.lean#L19-L50).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Alternative.lean#L19-L50.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, sections “Tensors”,
“The metrics of the spectral points” and “Flat or contracting”, and Appendix N. Source:
`anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/`, Apache-2.0. -/
namespace Ov

open Finset

/-- A tensor over the parties I with entries in K: for each party p a finite index set ι p, and an
array. The zero array is allowed. -/
structure Ten (K : Type) (I : Type) where
  ι : I → Type
  [fin : ∀ p, Fintype (ι p)]
  [dec : ∀ p, DecidableEq (ι p)]
  val : (∀ p, ι p) → K

attribute [instance] Ten.fin Ten.dec

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Linear maps on the legs, as matrices: from the legs of t to the legs of s. -/
abbrev Loc (s t : Ten K I) : Type := ∀ p, s.ι p → t.ι p → K

/-- The array obtained from t by the local maps L. -/
def app {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : K :=
  ∑ y : ∀ p, t.ι p, (∏ p, L p (x p) (y p)) * t.val y

/-- s is a restriction of t: s arises from t by local maps. -/
def Restr (s t : Ten K I) : Prop := ∃ L : Loc s t, ∀ x, s.val x = app L x

/-- s is covered by the tensors b k: it is a sum of restrictions of them. There is one
restriction of each b k; it may be 0. -/
def SumRestr {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I) : Prop :=
  ∃ L : ∀ k, Loc s (b k), ∀ x, s.val x = ∑ k, app (L k) x

/-- s and t are restrictions of one another. (The paper identifies such tensors.) -/
def Equi (s t : Ten K I) : Prop := Restr s t ∧ Restr t s

/-- The tensor 1: all legs one-dimensional, the entry 1. -/
def one : Ten K I where
  ι := fun _ => Unit
  val := fun _ => 1

instance : One (Ten K I) := ⟨one⟩

/-- The product (Kronecker product, party by party). -/
def mul (s t : Ten K I) : Ten K I where
  ι := fun p => s.ι p × t.ι p
  val := fun x => s.val (fun p => (x p).1) * t.val (fun p => (x p).2)

instance : Mul (Ten K I) := ⟨mul⟩

/-- The k-th power: indices are k-tuples. -/
def kpow (t : Ten K I) (k : ℕ) : Ten K I where
  ι := fun p => Fin k → t.ι p
  val := fun x => ∏ i, t.val (fun p => x p i)

/-- The product of a finite family. -/
def prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) : Ten K I where
  ι := fun p => ∀ k, (b k).ι p
  val := fun x => ∏ k, (b k).val (fun p => x p k)

/-- The push-forward πt: the index j of a tensor on J is given to the party π j. A party may get several
indices, or none (then its index set has one element). -/
def push (π : J → I) (t : Ten K J) : Ten K I where
  ι := fun q => ∀ j : {j : J // π j = q}, t.ι j.1
  val := fun x => t.val (fun j => x (π j) ⟨j, rfl⟩)

/-- The unit tensor ⟨r⟩_J of size r on J. -/
def unit (K : Type) [Field K] (J : Type) [Fintype J] [DecidableEq J] (r : ℕ) : Ten K J where
  ι := fun _ => Fin r
  val := fun x => if ∀ i j, x i = x j then 1 else 0

/-- The wire ⟨n⟩_pq of dimension n between p and q. If p = q and n > 0 it is equivalent to 1. -/
def wire (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I) : Ten K I :=
  push ![p, q] (unit K (Fin 2) n)

/-- A tensor has rank at most r if it is a restriction of the unit tensor of size r. (If there is a
party, this is the same as being a sum of r products of vectors: `rankLE_iff`.) -/
def RankLE (t : Ten K I) (r : ℕ) : Prop := Restr t (unit K I r)

end Ten

/-- A spectral point over the parties I: a real function F ≥ 0 on the tensors over I that is
multiplicative, with F(1) = 1 and F(s) ≤ ∑ F(b k) whenever s is a sum of restrictions of the b k. This
is the paper's definition, a multiplicative gauge; with the empty family it gives F(0) = 0. -/
structure Spec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  F : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ F t
  one : F 1 = 1
  mul : ∀ s t, F (s * t) = F s * F t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b → F s ≤ ∑ k, F (b k)

namespace Spec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- The paper's d_φ(p,q), the exponent of a wire: log₂ of the value at the wire of dimension 2 between p and q. -/
noncomputable def e (F : Spec K I) (p q : I) : ℝ := Real.logb 2 (F.F (Ten.wire K 2 p q))

end Spec

end Ov

namespace Nc.Price
open Ov Finset
variable (K : Type) [Field K]
/-- The multiples of the metrics of spectral points. -/
def specCone (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) :=
  {d | ∃ (F : Spec K V) (c : ℝ), 0 ≤ c ∧ d = fun u v => c * F.e u v}

/-- The prices of a finite set of parties. -/
def Prices (V : Type) [Fintype V] [DecidableEq V] : Set (V → V → ℝ) := closure (specCone K V)

/-- A function w on pairs of a set Y is a price if all its pull-backs to finite sets are. -/
def IsPrice {Y : Type*} (w : Y → Y → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Fin n → Y), (fun i j => w (f i) (f j)) ∈ Prices K (Fin n)

end Nc.Price

namespace Nc.Flag

open Nc.Price

/-- The flat case: all finite families of points of Euclidean spaces, with their distances, are prices. -/
def CaseOne (K : Type) [Field K] : Prop :=
  ∀ (k : ℕ) (V : Type) [Finite V] (E : V → EuclideanSpace ℝ (Fin k)),
    IsPrice K fun a b => dist (E a) (E b)


abbrev F2 := ZMod 2
abbrev Mt (m : ℕ) := Matrix (Fin m) (Fin m) F2
end Nc.Flag
namespace Paper
open Finset Nc.Price Nc.Flag
variable {μ : ℕ}
/-- The mean of |a, a+W|² over all matrices a and all matrices W of rank r: the square of the paper's D(r). -/
noncomputable def meanSq (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ :=
  (∑ a : Mt μ, ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = r), w a (a + W) ^ 2) /
    ((Fintype.card (Mt μ) : ℝ) * ((univ : Finset (Mt μ)).filter (fun W => W.rank = r)).card)

/-- The paper's D(r). -/
noncomputable def distAtRank (w : Mt μ → Mt μ → ℝ) (r : ℕ) : ℝ := √(meanSq w r)

/-- The flat case: "all finite subsets of all Euclidean spaces, with their metrics, are prices". -/
def Flat (K : Type) [Field K] : Prop := CaseOne K

/-- The contracting case: "there are an integer μ ≥ 2 and a real s with 1 ≤ s, s² < μ, such that D(μ) ≤ sD(1) for all
prices on Mat_μ(F₂)". -/
def Contracting (K : Type) [Field K] : Prop :=
  ∃ (μ : ℕ) (s : ℝ), 2 ≤ μ ∧ 1 ≤ s ∧ s ^ 2 < μ ∧
    ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1

end Paper


