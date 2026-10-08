-- Prove2me | Definitions.Def_TorsionFreeZeroDivisorsConstruction
-- name    : TorsionFreeZeroDivisorsConstruction
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T15:10:29.530244+00:00
-- url     : https://prove2.me/theorems/642ef0a2-f668-4b3d-97b1-732578c089c0
-- title:
--   OpenAI's torsion-free zero-divisor construction — prescribed types, random matchings, bounded systems, spherical pictures, the group $G$ and the factors $\alpha,\beta$
-- statement:
--   The definitions needed to state the lemmas of OpenAI's counterexample to Kaplansky's zero-divisor conjecture (*A Torsion-Free Group Algebra with Zero Divisors*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math)). They are taken from OpenAI's Lean development `lean/OAI/Algebra/GroupRing` (Apache License 2.0), with comments removed and identifier-level edits for this platform's Lean and Mathlib. They keep OpenAI's names in the namespace `OAI.TorsionFreeZeroDivisors`. The main objects follow, in the paper's order.
--
--   1. **Finite geometry and types (§2.1).** The projective plane over $\mathbb F_{128}$ has $16513$ points, and a point lies on a line when the dot product of representatives vanishes. The alphabet is the points together with three extra letters. Its inversion pairs each extra letter with a point and the remaining points in twos, through one fixed bijection (`Fintype.equivOfCardEq`); the paper pairs them “arbitrarily” (p. 4). At level $n$ the vertices of side $A$ and of side $B$ are triples (line, slot, copy) (`Types.VertexA`, `Types.VertexB`). The outgoing letters of a vertex are the points of its line together with the slot's extra letters: two extras on part of side $A$, all three on part of side $B$, as in conditions 1–3 of p. 4.
--
--   2. **Matchings and samples (§2.1, §2.3).** A matching is a fixed-point-free involution of the darts that sends each letter to its inverse (`ConditionedMatchings.Matching`). A sample is a pair of matchings, one per side, whose graphs have girth at least $L=\lfloor\ln(\mathrm{size}(n))/100\rfloor$, where $\mathrm{size}(n)=2\cdot16513^2n$ (`ActualPatternEvent.Match`, `ActualPatternEvent.samples`, `GirthAsymptotics.L`, `TypedGraphs.size`). Girth is measured in the subdivision graph, where it reads $\ge3L$. `GraphSample.Diameters` is the diameter event of Lemma 2.3, and `TypedDiameter.ΩA`, `ΩB`, `diameterBadA`, `diameterBadB` are the sets in which it is measured.
--
--   3. **Port graphs (§1, “Conventions”).** A port graph is an origin map on darts with a fixed-point-free reversal (`PortSubdivision.PortGraph`). The sampled graph $\Gamma=\Gamma_A\sqcup\Gamma_B$ is `SampleGraph.graph`, with letter labels `SampleGraph.label`.
--
--   4. **Bounded systems and patterns (§3).** `SampleGraph.BoundedSystem` is a finite family of non-backtracking paths in the sampled graph: closed except one optional root path at $x$ or $y$, with bounded number and total length. Its positions are paired by interval comparisons (`ComparedBlocks.Comparisons`) with the reduction condition (3.1) and at most $\varepsilon$ times the length unpaired. `BoundedPattern.Data`, `Data.Good` and `Data.event` are the abstract bounded patterns, their goodness and their realization in a sample. `PatternUniform.Ready` and `PatternTotalCoding.coefficient` are the numerical side conditions and the coding count of the union bound. `PlanarParameters` holds the constants (4.3) of Section 4.
--
--   5. **Planar separation (§4.3).** `RecursiveSeparator.Split` is one Lipton–Tarjan step: a removed set of size at most $2\sqrt2\sqrt{|S|}$ and parts of size at most $\tfrac23|S|$, each closed under a relation. `MapEuler.GenusZero` is the genus-zero (Euler) equation $2c(\sigma)+2c(\alpha\sigma)=|\operatorname{supp}\alpha|+4k(\sigma,\alpha)$ for a rotation and a pairing. `BoundaryRotation.perm` and `PairingClusters.Rel` are the boundary rotation and the cluster relation.
--
--   6. **Spherical pictures (Definition 4.1, §5).** `SphericalPicture.Data` is a combinatorial spherical picture over a labelled port graph. It consists of a rotation, a fixed-point-free pairing of positions with inverse letters, and darts forming closed paths, subject to the genus-zero equation. `Data.Reduced` asks that paired darts are never mutually reverse and that no path backtracks.
--
--   7. **The group and the factors (§5, §6).** `GraphPresentation.Routes` chooses a base vertex per component and a path to each vertex. `GraphPresentation.Group` is the presented group in which each dart's label equals the route labels at its ends, so that labels of closed paths are trivial: $\Gamma$ coned off. `ConcreteGroup.G` is that group for a sample, with routes fixed by choice. `ConcreteFactors.alpha` and `beta` are $\alpha=\sum_a g_a$ and $\beta=\sum_b h_b^{-1}$ in $\mathbb F_2[G]$ (`MonoidAlgebra (ZMod 2)`), over the components of the roots.
--
--   The bundle also contains the auxiliary definitions these depend on (chains, stages, grids, constants) and the few lemmas their definitions need.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, Sections 2-6, pp. 3-24 (the prescribed types, random matchings, bounded path systems, spherical arrangements, graph presentations and the factors α, β); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0)

import Mathlib

/-!
# The torsion-free zero-divisor construction: definitions

OpenAI, *A Torsion-Free Group Algebra with Zero Divisors*, OpenAI Math Release, September 23,
2026, https://github.com/openai/math (paper:
`preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf`).

The definitions, structures and instances below, with the few lemmas they need, are taken
from OpenAI's Lean development `lean/OAI/Algebra/GroupRing` in that repository (Apache
License, Version 2.0), with comments removed and identifier-level edits for this Lean and
Mathlib version. They are the declarations needed to state the published lemmas of the
construction, together with instances on them.
-/

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockGrid

def cell (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  ⟨⌊(N : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg x))).mpr
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one x) (Nat.cast_pos.mpr hN)⟩

theorem same_cell {N : ℕ} (hN : 0 < N) {x y : ℝ} (he : cell N hN x = cell N hN y) :
    |Int.fract x - Int.fract y| < 1 / (N : ℝ) := by
  have hf := congrArg Fin.val he
  dsimp [cell] at hf
  have hx0 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg x))
  have hy0 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg y))
  have hx1 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract x)
  have hy1 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract y)
  rw [hf] at hx0 hx1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [abs_lt]
  constructor
  · apply (neg_lt_iff_pos_add).mpr
    apply (mul_pos_iff_of_pos_left hNr).mp
    have hi : (N : ℝ) * (1 / N) = 1 := by field_simp
    nlinarith
  · apply (lt_div_iff₀ hNr).mpr
    nlinarith

theorem simultaneous {d N : ℕ} (hN : 0 < N) (a : Fin d → ℝ) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ N ^ d ∧
      ∃ z : Fin d → ℤ, ∀ i, |(u : ℝ) * a i - (z i : ℝ)| < 1 / (N : ℝ) := by
  classical
  let code : Fin (N ^ d + 1) → (Fin d → Fin N) :=
    fun k i => cell N hN ((k.val : ℝ) * a i)
  obtain ⟨j, k, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt code (by simp)
  have diff (j k : Fin (N^d+1)) (hjk : j.val < k.val) (he : code j = code k) :
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ N^d ∧
        ∃ z : Fin d → ℤ, ∀ i, |(u : ℝ)*a i - (z i : ℝ)| < 1/(N : ℝ) := by
    refine ⟨k.val-j.val, by omega, by omega,
      (fun i => ⌊(k.val : ℝ)*a i⌋ - ⌊(j.val : ℝ)*a i⌋), ?_⟩
    intro i
    have hi := same_cell hN (congrFun he i).symm
    have hcast : ((k.val-j.val : ℕ) : ℝ) = (k.val : ℝ) - j.val :=
      Nat.cast_sub (Nat.le_of_lt hjk)
    simpa only [code] using (by
      rw [hcast, Int.cast_sub]
      convert hi using 1
      simp only [Int.fract]
      ring_nf)
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hjk | hkj
  · exact diff j k hjk he
  · exact diff k j hkj he.symm

end TorsionFreeZeroDivisors.BlockGrid

namespace TorsionFreeZeroDivisors.BlockAlignment

section
open scoped Classical

def positions (lo hi : ℝ) : Finset ℤ := Finset.Ico ⌈lo-1/2⌉ ⌈hi-1/2⌉

theorem mem_positions {lo hi : ℝ} {q : ℤ} :
    q ∈ positions lo hi ↔ lo ≤ (q : ℝ)+1/2 ∧ (q : ℝ)+1/2 < hi := by
  simp only [positions,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

def affine (reverse : Bool) (a q : ℤ) : ℤ := if reverse then a-1-q else q+a

end

open scoped Classical BigOperators

end TorsionFreeZeroDivisors.BlockAlignment

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.EntropyStages
structure Pairing (O : Type*) where
  partner : O → O
  involutive : Function.Involutive partner
end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors.OccurrenceMatching
open scoped Classical
open EntropyStages
variable {Ω B E : Type*}

namespace Data

open scoped BigOperators
variable [Fintype Ω] [Fintype B]

end Data
end TorsionFreeZeroDivisors.OccurrenceMatching

namespace TorsionFreeZeroDivisors.ComparedBlocks
open scoped Classical BigOperators
open BlockAlignment EntropyStages
variable {T E : Type*}

abbrev Position (len : T → ℕ) := (t : T) × (positions 0 (len t))

variable (s : ℝ) (hs : 0 < s) (len : T → ℕ)

structure Comparisons where
  pairing : Pairing (Position len)
  side : Position len → Option E
  flip : E → E
  flip_inv : Function.Involutive flip
  flip_ne : ∀ e, flip e ≠ e
  side_partner : ∀ x e, side x = some e → side (pairing.partner x) = some (flip e)
  none_iff : ∀ x, side x = none ↔ pairing.partner x = x
  source : E → T
  lo : E → ℝ
  hi : E → ℝ
  reverse : E → Bool
  offset : E → ℤ
  side_iff : ∀ x e, side x = some e ↔ x.1 = source e ∧ x.2.val ∈ positions (lo e) (hi e)
  partner_source : ∀ x e, side x = some e → (pairing.partner x).1 = source (flip e)
  partner_coordinate : ∀ x e, side x = some e →
    (pairing.partner x).2.val = affine (reverse e) (offset e) x.2.val
  target_range : ∀ e, if reverse e then
      0 ≤ (offset e : ℝ)-hi e ∧ (offset e : ℝ)-lo e ≤ len (source (flip e))
    else 0 ≤ lo e+(offset e : ℝ) ∧ hi e+(offset e : ℝ) ≤ len (source (flip e))

namespace Comparisons
variable (C : Comparisons (E := E) len) (err : ℕ)

variable [Fintype T] [Fintype E]

end Comparisons
end TorsionFreeZeroDivisors.ComparedBlocks

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.AffineIntervals
open scoped Classical
open BlockAlignment

lemma integer_positions (a b : ℤ) : positions a b=Finset.Ico a b := by
  ext x
  rw [mem_positions,Finset.mem_Ico]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · by_contra h
      have : x+1≤a := by omega
      have : (x:ℝ)+1≤a := by exact_mod_cast this
      linarith
    · by_contra h
      have : b≤x := by omega
      have : (b:ℝ)≤x := by exact_mod_cast this
      linarith
  · rintro ⟨h1,h2⟩
    have h1' : (a:ℝ)≤x := by exact_mod_cast h1
    have h2' : (x:ℝ)+1≤b := by exact_mod_cast (show x+1≤b by omega)
    constructor <;> linarith

lemma nat_positions (n : ℕ) : positions 0 (n : ℝ)=Finset.Ico (0:ℤ) (n:ℤ) := by
  simpa only [Int.cast_zero,Int.cast_natCast] using integer_positions (0:ℤ) (n:ℤ)

end TorsionFreeZeroDivisors.AffineIntervals
namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open BlockAlignment ComparedBlocks AffineIntervals EntropyStages

variable {P T E : Type*} {lp : P → ℕ} {lt : T → ℕ}

namespace Chunking
variable (C : Comparisons (E := E) lp)

variable (lo hi : E → ℤ)

variable (hlo : ∀ e, C.lo e=(lo e : ℝ)) (hhi : ∀ e, C.hi e=(hi e : ℝ))

end Chunking
end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.FiniteChunking
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks AffineIntervals ChunkComparisons

variable {n : ℕ}

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

abbrev Traversal := (p : P) × Fin (chunks p)
def pathLength (p : P) : ℕ := ∑ i,len p i

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision

structure PortGraph (V D : Type*) where
  origin : D → V
  reverse : D → D
  reverse_reverse : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d

namespace PortGraph
variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem reverse_reverse_apply (d : D) : Γ.reverse (Γ.reverse d) = d :=
  Γ.reverse_reverse d

def subdivision : SimpleGraph (V ⊕ D) where
  Adj a b := match a,b with
    | .inl _, .inl _ => False
    | .inl v, .inr d => Γ.origin d = v
    | .inr d, .inl v => Γ.origin d = v
    | .inr d, .inr e => Γ.reverse d = e
  symm := ⟨by
    intro a b h
    cases a with
    | inl v => cases b <;> exact h
    | inr d =>
      cases b with
      | inl v => exact h
      | inr e =>
        change Γ.reverse e = d
        change Γ.reverse d = e at h
        rw [← h,Γ.reverse_reverse]⟩
  loopless := ⟨by
    intro a h
    cases a with
    | inl v => exact h
    | inr d => exact Γ.reverse_ne d h⟩

section Switching
variable [DecidableEq D]

end Switching

namespace Walk
variable {Γ} {a b c : V}

end Walk
end PortGraph
end TorsionFreeZeroDivisors.PortSubdivision

namespace TorsionFreeZeroDivisors.GirthSwitch

open SimpleGraph
open scoped ENNReal

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

end TorsionFreeZeroDivisors.GirthSwitch

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

@[reducible] def Chain (D : Type*) : ℕ → Type _
  | 0 => D
  | k+1 => D × Chain D k

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

variable {T}

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

def step (d e : D) : Prop := origin (rev d) = origin e ∧ e ≠ rev d

include hinv

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore
open SimpleGraph WeightedMoore PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.WeightedPortMoore

namespace TorsionFreeZeroDivisors.ChainSuppression
open Function
open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

def next : D → D := τ ∘ σ

include hσ hτ

lemma next_injective : Injective (next σ τ) := hτ.injective.comp hσ.injective

lemma folded_step (x : D) : next σ τ (τ (next σ τ x)) = τ x := by
  change τ (σ (τ (τ (σ x)))) = τ x
  rw [hτ (σ x),hσ x]

lemma folded_iterate (n : ℕ) (x : D) :
    (next σ τ)^[n] (τ ((next σ τ)^[n] x)) = τ x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply,ih,folded_step σ τ hσ hτ]

lemma reverse_segment {k i : ℕ} (hi : i ≤ k) (x : D) :
    (next σ τ)^[i] (τ ((next σ τ)^[k] x)) =
      τ ((next σ τ)^[k-i] x) := by
  have hk : k=i+(k-i) := by omega
  conv_lhs => rw [hk]
  rw [iterate_add_apply,folded_iterate σ τ hσ hτ]

variable [Finite D]

lemma exists_positive_return (x : D) (hx : τ x=x) :
    ∃ n : ℕ, 0<n ∧ τ ((next σ τ)^[n] x) = (next σ τ)^[n] x := by
  obtain ⟨n,hn,hp⟩ := (next_injective σ τ hσ hτ).mem_periodicPts x
  exact ⟨n,hn,by simpa only [hp.eq] using hx⟩

def length (x : D) (hx : τ x=x) : ℕ :=
  Nat.find (exists_positive_return σ τ hσ hτ x hx)

lemma length_pos (x : D) (hx : τ x=x) : 0 < length σ τ hσ hτ x hx :=
  (Nat.find_spec (exists_positive_return σ τ hσ hτ x hx)).1

lemma length_fixed (x : D) (hx : τ x=x) :
    τ ((next σ τ)^[length σ τ hσ hτ x hx] x) =
      (next σ τ)^[length σ τ hσ hτ x hx] x :=
  (Nat.find_spec (exists_positive_return σ τ hσ hτ x hx)).2

lemma no_internal_mark (x : D) (hx : τ x=x) {i : ℕ}
    (hi : 0 < i) (hik : i < length σ τ hσ hτ x hx) :
    τ ((next σ τ)^[i] x) ≠ (next σ τ)^[i] x := by
  intro he
  exact (not_lt_of_ge (Nat.find_min' (exists_positive_return σ τ hσ hτ x hx)
    ⟨hi,he⟩)) hik

def endpoint (x : {x : D // τ x=x}) : {x : D // τ x=x} :=
  ⟨(next σ τ)^[length σ τ hσ hτ x x.property] x,
    length_fixed σ τ hσ hτ x x.property⟩

lemma endpoint_reverse {x : {x : D // τ x=x}} {i : ℕ}
    (hi : i ≤ length σ τ hσ hτ x x.property) :
    (next σ τ)^[i] (endpoint σ τ hσ hτ x).val =
      τ ((next σ τ)^[length σ τ hσ hτ x x.property-i] x.val) := by
  have h := reverse_segment σ τ hσ hτ hi x.val
  rw [length_fixed σ τ hσ hτ x x.property] at h
  exact h

lemma endpoint_return (x : {x : D // τ x=x}) :
    (next σ τ)^[length σ τ hσ hτ x.val x.property] (endpoint σ τ hσ hτ x).val = x.val := by
  simpa only [Nat.sub_self,iterate_zero,id_eq,x.property] using
    (endpoint_reverse σ τ hσ hτ (x := x) (i := length σ τ hσ hτ x x.property) le_rfl)

lemma length_endpoint (x : {x : D // τ x=x}) :
    length σ τ hσ hτ (endpoint σ τ hσ hτ x).val (endpoint σ τ hσ hτ x).property =
      length σ τ hσ hτ x.val x.property := by
  let e := endpoint σ τ hσ hτ x
  let k := length σ τ hσ hτ x.val x.property
  let l := length σ τ hσ hτ e.val e.property
  have hk : 0<k := length_pos σ τ hσ hτ x.val x.property
  have hl : 0<l := length_pos σ τ hσ hτ e.val e.property
  have hret : (next σ τ)^[k] e.val=x.val := endpoint_return σ τ hσ hτ x
  have hle : l ≤ k := Nat.find_min' (exists_positive_return σ τ hσ hτ e.val e.property)
    ⟨hk,by rw [hret]; exact x.property⟩
  have heq : l=k := by
    by_contra he
    have hlt : l<k := lt_of_le_of_ne hle he
    have hr := endpoint_reverse σ τ hσ hτ (x := x) (i := l) hle
    have hef := length_fixed σ τ hσ hτ e.val e.property
    change τ ((next σ τ)^[l] e.val) = (next σ τ)^[l] e.val at hef
    rw [hr,hτ] at hef
    exact no_internal_mark σ τ hσ hτ x.val x.property (by omega : 0<k-l)
      (by omega : k-l<k) hef.symm
  exact heq

lemma endpoint_involutive : Involutive (endpoint σ τ hσ hτ) := by
  intro x
  apply Subtype.ext
  change (next σ τ)^[length σ τ hσ hτ (endpoint σ τ hσ hτ x).val
    (endpoint σ τ hσ hτ x).property] (endpoint σ τ hσ hτ x).val=x.val
  rw [length_endpoint]
  exact endpoint_return σ τ hσ hτ x

lemma endpoint_ne (hσne : ∀ d, σ d≠d) (x : {x : D // τ x=x}) :
    endpoint σ τ hσ hτ x ≠ x := by
  intro he
  let k := length σ τ hσ hτ x.val x.property
  have hk : 0<k := length_pos σ τ hσ hτ x.val x.property
  have hr (i : ℕ) (hi : i ≤ k) :
      (next σ τ)^[i] x.val=τ ((next σ τ)^[k-i] x.val) := by
    simpa only [he] using endpoint_reverse σ τ hσ hτ (x := x) hi
  rcases Nat.mod_two_eq_zero_or_one k with hp | hp
  · have hd : k-k/2=k/2 := by omega
    have hi : 0<k/2 := by omega
    have hit : k/2<k := by omega
    have hm := hr (k/2) (by omega)
    rw [hd] at hm
    exact no_internal_mark σ τ hσ hτ x.val x.property hi hit hm.symm
  · have hd : k-k/2=k/2+1 := by omega
    have hm := hr (k/2) (by omega)
    rw [hd,iterate_succ_apply'] at hm
    change (next σ τ)^[k/2] x.val = τ (τ (σ ((next σ τ)^[k/2] x.val))) at hm
    rw [hτ] at hm
    exact hσne _ hm.symm

end TorsionFreeZeroDivisors.ChainSuppression

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DegreeTwoSuppression
open Function
open scoped Classical
open TorsionFreeZeroDivisors ChainSuppression PortSubdivision
variable {V D : Type*} [Fintype D]

def out (o : D → V) (v : V) : Finset D := Finset.univ.filter (fun d => o d=v)
@[simp] lemma mem_out (o : D → V) (v : V) (d : D) : d∈out o v ↔ o d=v := by
  simp [out]

lemma unique_other (o : D → V) (d : D) (hc : (out o (o d)).card=2) :
    ∃! e : D, o e=o d ∧ e≠d := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hc
  have hm (e : D) : o e=o d ↔ e=a ∨ e=b := by
    rw [← mem_out,hs]
    simp
  have hd : d=a ∨ d=b := (hm d).mp rfl
  rcases hd with rfl | rfl
  · refine ⟨b,⟨(hm b).mpr (Or.inr rfl),Ne.symm hab⟩,?_⟩
    intro e he
    exact ((hm e).mp he.1).resolve_left he.2
  · refine ⟨a,⟨(hm a).mpr (Or.inl rfl),hab⟩,?_⟩
    intro e he
    exact ((hm e).mp he.1).resolve_right he.2

variable (o : D → V) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out o v).card=2)

def turn (d : D) : D := if h : mark (o d) then d else
  Classical.choose (unique_other o d (h2 (o d) h)).exists

lemma turn_of_mark (d : D) (hd : mark (o d)) : turn o mark h2 d=d := by
  simp [turn,hd]

lemma turn_of_unmarked (d : D) (hd : ¬mark (o d)) :
    o (turn o mark h2 d)=o d ∧ turn o mark h2 d≠d := by
  simpa only [turn,dif_neg hd] using
    Classical.choose_spec (unique_other o d (h2 (o d) hd)).exists

lemma turn_involutive : Involutive (turn o mark h2) := by
  intro d
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd,turn_of_mark o mark h2 d hd]
  · have he := turn_of_unmarked o mark h2 d hd
    have hemark : ¬mark (o (turn o mark h2 d)) := he.1 ▸ hd
    have hef := turn_of_unmarked o mark h2 (turn o mark h2 d) hemark
    exact (unique_other o (turn o mark h2 d) (h2 _ hemark)).unique hef
      ⟨he.1.symm,he.2.symm⟩

def suppressed (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2) :
    PortGraph V {d : D // turn Γ.origin mark h2 d=d} where
  origin d := Γ.origin d.val
  reverse := endpoint Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2)
  reverse_reverse := endpoint_involutive Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
  reverse_ne := endpoint_ne Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) Γ.reverse_ne

def chainLength (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : ℕ :=
  length Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) d.val d.property

end TorsionFreeZeroDivisors.DegreeTwoSuppression

namespace TorsionFreeZeroDivisors.SuppressedMoore
open Function SimpleGraph
open scoped Classical
open TorsionFreeZeroDivisors PortSubdivision WeightedMoore
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)

local notation "τ" => DegreeTwoSuppression.turn Γ.origin mark h2
local notation "hτ" => DegreeTwoSuppression.turn_involutive Γ.origin mark h2
local notation "F" => ChainSuppression.next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "Γ'" => DegreeTwoSuppression.suppressed Γ mark h2
local notation "len" => DegreeTwoSuppression.chainLength Γ mark h2

def iterChain (f : D → D) : (n : ℕ) → D → Chain D n
  | 0, x => x
  | n+1, x => (x,iterChain f n (f x))

omit [Fintype D] in
def outWord : {k : ℕ} → Chain D k → List D
  | 0, d => [d]
  | _+1, p => p.1 :: outWord p.2

end TorsionFreeZeroDivisors.SuppressedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainCoverage
open Function ChainSuppression
open scoped Classical
variable {D : Type*} [Finite D] (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

def Covered (d : D) : Prop :=
  ∃ (x : {x : D // τ x = x}) (i : Fin (length σ τ hσ hτ x.val x.property)),
    (next σ τ)^[i.val] x.val = d

end TorsionFreeZeroDivisors.ChainCoverage

namespace TorsionFreeZeroDivisors.ActualMarkedChains
open Function PortSubdivision ChainSuppression DegreeTwoSuppression ChainCoverage
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)

end TorsionFreeZeroDivisors.ActualMarkedChains

namespace TorsionFreeZeroDivisors.MarkedChainBound
open PortSubdivision DegreeTwoSuppression
open scoped Classical BigOperators
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.MarkedChainBound

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

def word (d : B) : List D := outWord (iterChain F (len d-1) d.val)

end TorsionFreeZeroDivisors.ChainPaths

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical

end TorsionFreeZeroDivisors.IntervalSelfLinks

namespace TorsionFreeZeroDivisors.EntropyStages

open scoped BigOperators

namespace Pairing

variable {O C : Type*} [Fintype O] [DecidableEq O] [DecidableEq C] (P : Pairing O)

end Pairing

end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors
open scoped BigOperators

end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.StageFusion

section
open scoped BigOperators
open EntropyStages

section Components
variable {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]

end Components

def epsilon (δ a : ℝ) : ℝ := min (1/4) (δ/(16*(1+a)))

end

open scoped Classical BigOperators

section FiniteProbability
variable {Ω P : Type*} [Fintype P] (sample : Finset Ω) (hsample : sample.Nonempty)

end FiniteProbability

end TorsionFreeZeroDivisors.StageFusion

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.IncidenceStages
open scoped Classical BigOperators
open EntropyStages
variable {O D V : Type*} [Fintype O] [Fintype D] [Fintype V]

namespace Passages
variable {origin : D → V} {port : O → D}

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision
variable {V D T : Type*}

abbrev Matching (label : D → T) (bar : T → T) :=
  {r : Equiv.Perm D // Function.Involutive r ∧
    (∀ x, r x ≠ x) ∧ ∀ x, label (r x) = bar (label x)}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance [Fintype D] : Fintype (Matching label bar) := by
  classical
  unfold Matching
  infer_instance
instance : DecidableEq (Matching label bar) := Classical.decEq _

def graph (r : Matching label bar) (origin : D → V) : PortGraph V D :=
  ⟨origin,r,r.property.1,r.property.2.1⟩

@[simp] theorem reverse_reverse (r : Matching label bar) (x : D) : r (r x) = x := r.property.1 x

variable [DecidableEq D]

def Contains (r : Matching label bar) (C : Finset (Sym2 D)) : Prop :=
  ∀ a b, s(a,b) ∈ C → r a = b

variable [Fintype V] [Fintype D]

def conditioned (origin : D → V) (N : ℕ) (C : Finset (Sym2 D)) :
    Finset (Matching label bar) := by
  classical
  exact Finset.univ.filter fun r => r.Contains C ∧
    (N : ℕ∞) ≤ (r.graph origin).subdivision.egirth

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternCount
open scoped Classical
open ConditionedMatchings
variable {V D T F E A : Type*} [Fintype V] [Fintype D] [Fintype F] [Fintype E]
variable (label : D → T) (bar : T → T)

end TorsionFreeZeroDivisors.PatternCount

namespace TorsionFreeZeroDivisors.PatternEmbeddings
open scoped BigOperators Classical
open PortSubdivision ConditionedMatchings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

abbrev Dart (outgoing : TV → Finset T) := {x : TV × T // x.2 ∈ outgoing x.1}
def origin (outgoing : TV → Finset T) (e : Dart outgoing) : TV := e.val.1
def label (outgoing : TV → Finset T) (e : Dart outgoing) : T := e.val.2

variable (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
  (allowed : PV → Finset TV)
  (hallowed : ∀ v x, x ∈ allowed v → ∀ d, Γ.origin d = v → plabel d ∈ outgoing x)

end TorsionFreeZeroDivisors.PatternEmbeddings

namespace TorsionFreeZeroDivisors
namespace Types

open scoped LinearAlgebra.Projectivization
open Configuration

abbrev Field128 := GaloisField 2 7

instance : Fintype Field128 := Fintype.ofFinite _
instance : DecidableEq Field128 := Classical.decEq _

abbrev Point := ℙ Field128 (Fin 3 → Field128)
abbrev Line := Point

instance : Fintype Point := Fintype.ofFinite _
instance : DecidableEq Point := Classical.decEq _

instance (p : Point) (l : Line) : Decidable (p ∈ l) := Classical.propDecidable _

theorem field_card : Nat.card Field128 = 128 := by
  simpa using GaloisField.card 2 7 (by decide)

theorem point_card : Fintype.card Point = 16513 := by
  have h := Projectivization.card' Field128 (Fin 3 → Field128)
  rw [Nat.card_fun, Nat.card_fin, field_card] at h
  change 128 ^ 3 = Nat.card Point * (128 - 1) + 1 at h
  norm_num at h
  omega

def pointsOn (l : Line) : Finset Point := Finset.univ.filter (· ∈ l)

abbrev SlotA := (Fin 3 × Fin 129) ⊕ Fin 32639
abbrev SlotB := Fin 258 ⊕ Fin 32768
abbrev VertexA (N : ℕ) := Line × SlotA × Fin N
abbrev VertexB (N : ℕ) := Line × SlotB × Fin N
abbrev Letter := Point ⊕ Fin 3

def extrasA : SlotA → Finset (Fin 3)
  | .inl (i, _) => Finset.univ.erase i
  | .inr _ => ∅

def extrasB : SlotB → Finset (Fin 3)
  | .inl _ => Finset.univ
  | .inr _ => ∅

def outgoingA {N : ℕ} (x : VertexA N) : Finset Letter :=
  (pointsOn x.1).disjSum (extrasA x.2.1)

def outgoingB {N : ℕ} (y : VertexB N) : Finset Letter :=
  (pointsOn y.1).disjSum (extrasB y.2.1)

abbrev OrdinaryCode := Fin 3 ⊕ (Fin 8255 × Bool)
abbrev Generator := Fin 3 ⊕ Fin 8255
abbrev Signed := Generator × Bool

def pointCode : Point ≃ OrdinaryCode := Fintype.equivOfCardEq (by
  rw [point_card]
  simp [OrdinaryCode])

def signedLetter : Signed ≃ Letter where
  toFun
    | (.inl i, true) => .inr i
    | (.inl i, false) => .inl (pointCode.symm (.inl i))
    | (.inr j, b) => .inl (pointCode.symm (.inr (j,b)))
  invFun
    | .inr i => (.inl i, true)
    | .inl p => match pointCode p with
      | .inl i => (.inl i, false)
      | .inr (j,b) => (.inr j, b)
  left_inv := by
    rintro ⟨i | j,b⟩ <;> cases b <;> simp
  right_inv := by
    rintro (p | i)
    · cases hc : pointCode p with
      | inl j =>
        simp only [hc]
        exact congrArg Sum.inl (pointCode.symm_apply_eq.mpr hc.symm)
      | inr jb =>
        simp only [hc]
        exact congrArg Sum.inl (pointCode.symm_apply_eq.mpr hc.symm)
    · rfl

def inverse (t : Letter) : Letter :=
  signedLetter ( (signedLetter.symm t).1, !(signedLetter.symm t).2 )

variable {V : Type*} (outgoing : V → Finset Letter)

end Types
end TorsionFreeZeroDivisors

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
namespace WordEstimate

open scoped BigOperators

abbrev Letter := (Fin 3 ⊕ Fin 8255) × Bool

end WordEstimate
end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.WordEstimate
open scoped BigOperators

end TorsionFreeZeroDivisors.WordEstimate

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ListPassages
open scoped Classical BigOperators

variable {D : Type*} (p : List D) (hp : p ≠ [])

end TorsionFreeZeroDivisors.ListPassages
namespace TorsionFreeZeroDivisors.ChainPathTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open WeightedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "w" => word Γ mark h2

end TorsionFreeZeroDivisors.ChainPathTransport
namespace TorsionFreeZeroDivisors.ListStageExponents
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

end TorsionFreeZeroDivisors.ListStageExponents

namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

def rank (d : D) : Fin (Fintype.card D) := Fintype.equivFin D d

def Chosen (d : D) : Prop := rank d < rank (σ d)
abbrev Representative := {d : D // Chosen σ d}

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

include hne in
lemma rank_ne (d : D) : rank d ≠ rank (σ d) := by
  intro h
  exact hne d ((Fintype.equivFin D).injective h).symm

include hσ hne

lemma chosen_or_reverse (d : D) : Chosen σ d ∨ Chosen σ (σ d) := by
  unfold Chosen
  rw [hσ]
  exact lt_or_gt_of_ne (rank_ne σ hne d)

lemma chosen_reverse_iff (d : D) : Chosen σ (σ d) ↔ ¬Chosen σ d := by
  unfold Chosen
  rw [hσ]
  exact ⟨fun h h' => (lt_asymm h h'),fun h => lt_of_le_of_ne (le_of_not_gt h) (rank_ne σ hne d).symm⟩

def orient (x : Representative σ × Bool) : D := if x.2 then σ x.1.val else x.1.val

lemma orient_injective : Function.Injective (orient σ) := by
  rintro ⟨⟨a,ha⟩,i⟩ ⟨⟨b,hb⟩,j⟩ he
  cases i <;> cases j
  · simp only [orient,Bool.false_eq_true,ite_false] at he
    cases he
    rfl
  · simp only [orient,Bool.false_eq_true,ite_false,ite_true] at he
    have hna := (chosen_reverse_iff σ hσ hne b).mp (he ▸ ha)
    exact (hna hb).elim
  · simp only [orient,Bool.false_eq_true,ite_false,ite_true] at he
    have hnb := (chosen_reverse_iff σ hσ hne a).mp (he.symm ▸ hb)
    exact (hnb ha).elim
  · simp only [orient,ite_true] at he
    have hab := hσ.injective he
    cases hab
    rfl

lemma orient_surjective : Function.Surjective (orient σ) := by
  intro d
  rcases chosen_or_reverse σ hσ hne d with hd|hd
  · exact ⟨(⟨d,hd⟩,false),rfl⟩
  · exact ⟨(⟨σ d,hd⟩,true),hσ d⟩

def equiv : Representative σ × Bool ≃ D :=
  Equiv.ofBijective (orient σ) ⟨orient_injective σ hσ hne,orient_surjective σ hσ hne⟩

end TorsionFreeZeroDivisors.InvolutionOrientation
namespace TorsionFreeZeroDivisors.ChainIsomorphism
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => InvolutionOrientation.Representative (PortGraph.reverse (suppressed Γ mark h2))
local notation "len" => chainLength Γ mark h2

abbrev Rep := R
abbrev Mark := {v : V // mark v}

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open ComparedBlocks
variable {P T U C : Type*} {lp : P → ℕ} {lt : T → ℕ}

namespace Chunking
end Chunking

variable [Fintype T] (color : T → C)
def multiplicity (c : C) : ℕ := Fintype.card {t // color t=c}

end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.ListChunkCoordinates
open scoped Classical BigOperators
open FiniteChunking
variable {A D : Type*} (ds : List A) (word : A → List D)

abbrev lengths (i : Fin ds.length) : ℕ := (word (ds.get i)).length

lemma ofFn_lengths : List.ofFn (lengths ds word)=ds.map (fun a => (word a).length) := by
  change List.ofFn (fun i : Fin ds.length => (word ds[i.val]).length) = _
  exact List.ofFn_getElem_eq_map ds (fun a => (word a).length)

lemma total_length : (∑ i,lengths ds word i)=(ds.flatMap word).length := by
  rw [← List.sum_ofFn,ofFn_lengths,List.length_flatMap]

end TorsionFreeZeroDivisors.ListChunkCoordinates

namespace TorsionFreeZeroDivisors.ChainChunkTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChunkComparisons FiniteChunking ComparedBlocks
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "len" => chainLength Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "w" => word Γ mark h2

def orientation : R × Bool ≃ B := InvolutionOrientation.equiv (S).reverse (S).reverse_reverse (S).reverse_ne

def representative (b : B) : R := ((orientation Γ mark h2).symm b).1

variable {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

def chunks (p : P) : ℕ := (paths p).length
def chunkLength (p : P) (i : Fin (chunks Γ mark h2 paths p)) : ℕ := (w ((paths p).get i)).length
def color (t : Traversal (chunks Γ mark h2 paths)) : R := representative Γ mark h2 ((paths t.1).get t.2)

omit [Fintype P] in
lemma pathLength_eq (p : P) :
    pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) p=((paths p).flatMap w).length :=
  ListChunkCoordinates.total_length (paths p) w

def originalDart (x : Position (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) : D :=
  ((paths x.1).flatMap w).get ⟨x.2.val.toNat,by
    have hx := x.2.property
    have hz : 0≤x.2.val ∧ x.2.val < pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths) x.1 := by
      simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hx
    rw [←pathLength_eq Γ mark h2 paths]
    omega⟩

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ChainChunkTransport

namespace TorsionFreeZeroDivisors.ChainMultiplicity
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

local notation "col" => color Γ mark h2 paths
local notation "tp" => Traversal (chunks Γ mark h2 paths)

end TorsionFreeZeroDivisors.ChainMultiplicity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainActiveStages
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainActiveStages

namespace TorsionFreeZeroDivisors.SubdivisionRestriction
open scoped Classical
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
    (active : C → Prop) (incident : V → Prop)
    (hf : ∀ c,active c → incident (first c))
    (hl : ∀ c,active c → incident (last c))

end TorsionFreeZeroDivisors.SubdivisionRestriction

namespace TorsionFreeZeroDivisors.ChainStageEmbedding
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths

end TorsionFreeZeroDivisors.ChainStageEmbedding

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical BigOperators
variable {V T : Type*} [Fintype V]

def pin (root : Option V) (target : T) (v : V) : Option T :=
  if root=some v then some target else none

end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.ActiveRoot
open scoped Classical
open PortSubdivision
variable {V D P : Type*} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])

end TorsionFreeZeroDivisors.ActiveRoot

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.LinkComponents
open scoped Classical BigOperators
open EntropyStages
variable {I : Type*} [Fintype I] (m : I → ℕ)

end TorsionFreeZeroDivisors.LinkComponents

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*}

end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.RepeatedBlocks
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {C E : Type*} (s : ℝ) (hs : 0 < s) (len m : C → ℕ)

abbrev Traversal := (c : C) × Fin (m c)

variable (err : ℕ)

variable {A : Type*} (symbol : E → (A ≃ A))

end TorsionFreeZeroDivisors.RepeatedBlocks

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

end

section Active
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

end Active
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)
local instance : DecidableEq Types.Letter := Classical.decEq _

end TorsionFreeZeroDivisors.StageExpectation

namespace TorsionFreeZeroDivisors.TwoSideMean
open scoped BigOperators Classical

variable {A B W : Type*}

end TorsionFreeZeroDivisors.TwoSideMean

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
open PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

variable (s : ℝ) (hs : 0 < s)

variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings
variable {V : Type*} (outgoing : V → Finset Letter)

abbrev Dart := {e : V × Letter // e.2 ∈ outgoing e.1}
def origin (e : Dart outgoing) : V := e.val.1
def label (e : Dart outgoing) : Letter := e.val.2

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

def L (n : ℕ) : ℕ := ⌊Real.log n / 100⌋₊

def exclusion (n : ℕ) : ℕ := 4 * 132 ^ (6 * L n + 1)

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedGraphs
open Filter GirthAsymptotics TorsionFreeZeroDivisors.Types ConditionedMatchings PortSubdivision
open scoped Topology

def size (rep : ℕ) : ℕ := 2 * 16513 ^ 2 * rep

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.TypedStage
open scoped Classical BigOperators Topology
open TorsionFreeZeroDivisors.Types TwoSideStage GirthAsymptotics Filter
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V : Type} [Fintype C] [Fintype V]
variable (rep : ℕ) (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.TypedStage

namespace TorsionFreeZeroDivisors.StageCost
open scoped BigOperators

end TorsionFreeZeroDivisors.StageCost

namespace TorsionFreeZeroDivisors.StageDenominator

section
open scoped Topology
open Filter GirthAsymptotics TypedGraphs

def carrier (rep : ℕ) : ℕ := 4260354*rep
def denominator (K rep : ℕ) : ℕ :=
  carrier rep - (K*L (size rep)+exclusion (size rep))

def penalty (K rep : ℕ) : ℝ := Real.log ((size rep:ℝ)*(129/16513)/(denominator K rep))

def error (K Q rep : ℕ) : ℝ :=
  Q*(-Real.log (129/16513)) + (K:ℝ)*L (size rep)*penalty K rep

end

open scoped BigOperators Topology
open Filter GirthAsymptotics TypedGraphs TwoSideStage

variable {C V : Type} [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageDenominator

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StageEntropy

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*}

variable [Fintype B]
end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.StageMass

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

variable [Fintype E]

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

end TorsionFreeZeroDivisors.StageMass

namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C]
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.GridAsymptotics
open Filter Topology
open scoped Classical

def exponent (d : ℕ) : ℝ := 1 / (2*((d : ℝ)+1))
def N (d : ℕ) (L : ℝ) : ℕ := ⌊L ^ exponent d⌋₊
def R (d : ℕ) (L : ℝ) : ℕ := ⌊Real.sqrt (N d L)⌋₊

theorem exponent_pos (d : ℕ) : 0 < exponent d := by unfold exponent; positivity

theorem N_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 < N d L := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow hL (exponent_pos d).le

def scale (d : ℕ) (L : ℝ) (u : ℕ) : ℝ := L / ((u : ℝ)*R d L)

def Compatible (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) (u : ℕ) : Prop :=
  1 ≤ u ∧ ∃ z : Fin d → ℤ, ∀ i,
    |(u : ℝ)*((offset i : ℝ)/L)-(z i : ℝ)| < 1/(N d L : ℝ)

theorem compatible_exists (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    ∃ u, Compatible d L offset u := by
  obtain ⟨u,hu,_,z,hz⟩ := BlockGrid.simultaneous (N_pos d hL) (fun i => (offset i : ℝ)/L)
  exact ⟨u,hu,z,hz⟩

def chosenU (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℕ :=
  if hL : 1 ≤ L then Nat.find (compatible_exists d hL offset) else 1

def chosenScale (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℝ :=
  scale d L (chosenU d L offset)

def letterError (d : ℕ) (L : ℝ) (offset : Fin d → ℤ) : ℕ :=
  ⌈2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4⌉₊

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

def rate (d : ℕ) (L : ℝ) : ℝ :=
  1/(R d L:ℝ)+1/Real.sqrt L+(R d L:ℝ)/(N d L)+1/L

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics Filter

def alphabetLog : ℝ := Real.log (Fintype.card WordEstimate.Letter)

def coefficient (D K M Q : ℕ) : ℝ :=
  256*(22*D+K)+(1/1200:ℝ)*M*Q+M*(10*K+2*Q)*alphabetLog

variable {C E : Type*} [Fintype C] [Fintype E]

open GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.StageUniform
namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

def binRate (L : ℝ) : ℝ := (Real.log 257+Real.log L)/Real.sqrt L

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

structure Embedding (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (bar : T → T) (r : Matching (label outgoing) bar) where
  vertex : PV ↪ TV
  port : PD ↪ Dart outgoing
  origin_eq : ∀ d, origin outgoing (port d) = vertex (Γ.origin d)
  label_eq : ∀ d, label outgoing (port d) = plabel d
  reverse_eq : ∀ d, r.val (port d) = port (Γ.reverse d)
  pin_eq : ∀ v y, pin v = some y → vertex v = y

variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

variable {PV' PD' : Type*} [Fintype PV'] [Fintype PD']

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T QV QD : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]
    [Fintype QV] [Fintype QD]
variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StagePartition

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.PartitionEntropy

namespace TorsionFreeZeroDivisors.SideRestriction
open scoped Classical
open PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D) (side : V → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

abbrev Vertex := {v : V // side v=b}
abbrev Dart := {d : D // side (Γ.origin d)=b}
def graph : PortGraph (Vertex side b) (Dart Γ side b) where
  origin d := ⟨Γ.origin d.val,d.property⟩
  reverse d := ⟨Γ.reverse d.val,(hs d.val).trans d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d.val)
  reverse_ne d h := Γ.reverse_ne d.val (congrArg Subtype.val h)

variable {QV QD : Type*} (Q : PortGraph QV QD) (fv : QV ↪ V) (fd : QD ↪ D)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d))
    (hf : ∀ v,side (fv v)=b)

variable [Fintype V] [Fintype D] [Fintype QV] [Fintype QD]
    {TV T : Type*} [Fintype TV] [Fintype T]
    (label : D → T) (outgoing : TV → Finset T) (pin : Vertex side b → Option TV)
    (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

end TorsionFreeZeroDivisors.SideRestriction

namespace TorsionFreeZeroDivisors.StageSideEmbedding
open scoped Classical BigOperators
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

variable [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageSideEmbedding

namespace TorsionFreeZeroDivisors.ChainSide
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical BigOperators
variable {V TA TB : Type*} [Fintype V] (side : V → Bool)

def root (r : Option V) (b : Bool) : Option {v : V // side v=b} :=
  r.bind fun v => if h : side v=b then some ⟨v,h⟩ else none

end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

def cyclic (root : Option P) (p : P) : Bool := decide (root≠some p)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
variable {V T : Type*}
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical
variable {V : Type*} (side : V → Bool)
end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2

def source (r : Option P) : Option V := r.map fun p => (S).origin ((paths p).head (hp p))

variable (side : V → Bool)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable {E : Type}

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

abbrev Match (rep : ℕ) :=
  ConditionedMatchings.Matching (PatternEmbeddings.label (@Types.outgoingA rep)) Types.inverse ×
  ConditionedMatchings.Matching (PatternEmbeddings.label (@Types.outgoingB rep)) Types.inverse

def samples (rep : ℕ) : Finset (Match rep) :=
  ConditionedMatchings.Matching.conditioned (label:=PatternEmbeddings.label (@Types.outgoingA rep))
    (bar:=Types.inverse) (PatternEmbeddings.origin (@Types.outgoingA rep))
    (3*GirthAsymptotics.L (TypedGraphs.size rep)) ∅ ×ˢ
  ConditionedMatchings.Matching.conditioned (label:=PatternEmbeddings.label (@Types.outgoingB rep))
    (bar:=Types.inverse) (PatternEmbeddings.origin (@Types.outgoingB rep))
    (3*GirthAsymptotics.L (TypedGraphs.size rep)) ∅

abbrev sourcePinA := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) true) a
abbrev sourcePinB := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) false) b

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

def Ready (K M Q J rep : ℕ) : Prop :=
  1 ≤ (L (size rep):ℝ) ∧ 0<size rep ∧
  K*L (size rep)+exclusion (size rep)<StageDenominator.carrier rep ∧
  GridUniform.binRate (L (size rep))≤1/(4800*M:ℝ) ∧
  ∀ d≤J,
    StageUniform.coefficient d K M Q*GridUniform.rate d (L (size rep))+
      M*StageDenominator.error K Q rep/(L (size rep):ℝ) ≤ 1/4800 ∧
    ∀ offset : Fin d → ℤ,3003≤chosenScale d (L (size rep)) offset ∧
      2*(letterError d (L (size rep)) offset:ℝ)<chosenScale d (L (size rep)) offset-1

variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

def Realized (patCmp : Comparisons (E:=E) pl) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    (∀ x e,patCmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if patCmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (patCmp.pairing.partner x))) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

variable [Fintype E]

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'}

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision.Iso
open scoped Classical
variable {V D V' D' T TV : Type*} [Fintype V] [Fintype D] [Fintype V'] [Fintype D'] [Fintype T] [Fintype TV] {Γ : PortGraph V D} {Γ' : PortGraph V' D'} (side : V → Bool) (side' : V' → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d)) (b : Bool) (root : Option V) (root' : Option V') (label : D' → T) (outgoing : TV → Finset T) (target : TV) (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

end TorsionFreeZeroDivisors.PortSubdivision.Iso

namespace TorsionFreeZeroDivisors.OriginalPatternIso
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
variable {V D P E V' D' P' E' : Type} [Fintype V] [Fintype D] [Fintype P]
    [Fintype V'] [Fintype D'] [Fintype P']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (paths' : P' → List {x : D' // turn Γ'.origin mark' h2' x=x}) (hp' : ∀ p,paths' p≠[])
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)
local notation "pl'" => pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')
variable (eP : P ≃ P')

variable (side : V → Bool) (side' : V' → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d)) (root : Option P) (root' : Option P') (C : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) (C' : Comparisons (E:=E') (pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths'))) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)

end TorsionFreeZeroDivisors.OriginalPatternIso

namespace TorsionFreeZeroDivisors.PatternCoding

section
open scoped BigOperators Classical

def coefficient (R K T I : ℕ) : ℕ :=
  R^(2*R) * 2^R * (R+1)^(T*K) * (1+2*K) * (1+2*K^2)^I

end

open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

variable {D V P J D' V' P' J' : Type*}
  [Fintype D] [Fintype V] [Fintype P] [Fintype J]
  [Fintype D'] [Fintype V'] [Fintype P'] [Fintype J']

variable (R K T I H : ℕ) (hR : 0<R)
  (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
  (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)

variable (hD' : Fintype.card D' ≤ R) (hV' : Fintype.card V' ≤ R)
  (hP' : Fintype.card P' ≤ K) (hJ' : Fintype.card J' ≤ I)

end TorsionFreeZeroDivisors.PatternCoding

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ComparisonCoding
open scoped Classical
open PatternCoding

def coefficient (K I : ℕ) := (8*I*K)^I

variable {P E P' E' : Type*} [Fintype P] [Fintype E] [Fintype P'] [Fintype E']
    (K I H : ℕ) (hK : 0<K) (hI : 0<I)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

variable (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

end TorsionFreeZeroDivisors.ComparisonCoding

namespace TorsionFreeZeroDivisors.SubdivisionIso
open scoped Classical
open PortSubdivision
variable {C V C' V' : Type*} (len : C → ℕ) (len' : C' → ℕ)
    (first last : C → V) (first' last' : C' → V')
    (eC : C ≃ C') (eV : V ≃ V') (hl : ∀ c,len c=len' (eC c))

variable (hf : ∀ c,eV (first c)=first' (eC c)) (ht : ∀ c,eV (last c)=last' (eC c))

end TorsionFreeZeroDivisors.SubdivisionIso

namespace TorsionFreeZeroDivisors.RankedSuppressionIso

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "R'" => Rep Γ' mark' h2'

variable (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
  (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
    Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)

end

section
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "F'" => next Γ'.reverse (turn Γ'.origin mark' h2')
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'

end

open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'

variable (side : V → Bool) (side' : V' → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))

variable {P P' : Type} (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (paths' : P' → List {d : D' // turn Γ'.origin mark' h2' d=d}) (eP : P ≃ P')

variable (hne : ∀ p,paths p≠[]) (hne' : ∀ p,paths' p≠[])
    (root : Option P) (root' : Option P') (hroot : root.map eP=root')

end TorsionFreeZeroDivisors.RankedSuppressionIso

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternTotalCoding
open scoped Classical
open PatternCoding

def coefficient (R K T I : ℕ) :=
  (R+1)^2*(K+1)*PatternCoding.coefficient R K T 0*2^R*(I+1)*ComparisonCoding.coefficient K I

variable {D V P E D' V' P' E' : Type*}
    [Fintype D] [Fintype V] [Fintype P] [Fintype E]
    [Fintype D'] [Fintype V'] [Fintype P'] [Fintype E']
    (R K T I H : ℕ) (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (hD : Fintype.card D≤R) (hV : Fintype.card V≤R)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

variable (hD' : Fintype.card D'≤R) (hV' : Fintype.card V'≤R)
    (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

end TorsionFreeZeroDivisors.PatternTotalCoding

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks

structure Data (R K T I H : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  mark : V → Prop
  degree_two : ∀ v,¬mark v → (out graph.origin v).card=2
  covered : ∀ d,ChainCoverage.Covered graph.reverse (turn graph.origin mark degree_two)
    graph.reverse_reverse (turn_involutive graph.origin mark degree_two) d
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List {d : D // turn graph.origin mark degree_two d=d}
  nonempty : ∀ p,paths p≠[]
  root : Option P
  comparisons : Comparisons (E:=E) (pathLength (chunks graph mark degree_two paths)
    (chunkLength graph mark degree_two paths))
  lower : E → Fin (H+1)
  upper : E → Fin (H+1)
  offset : E → Fin (4*H+1)
  lower_eq : ∀ e,comparisons.lo e=(lower e).val
  upper_eq : ∀ e,comparisons.hi e=(upper e).val
  offset_eq : ∀ e,comparisons.offset e=((offset e).val:ℤ)-2*H
  dart_bound : Fintype.card {d : D // turn graph.origin mark degree_two d=d}≤R
  vertex_bound : Fintype.card (Mark mark)≤R
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  chain_length_bound : ∀ d,chainLength graph mark degree_two d≤H
  traversal_bound : ∀ p,(paths p).length≤T

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {R K T I H : ℕ} (a : Data R K T I H)

end Data
end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.PatternFiniteUnion
open scoped Classical

end TorsionFreeZeroDivisors.PatternFiniteUnion

namespace TorsionFreeZeroDivisors.BoundedPattern.Data

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
variable {R K T I H : ℕ} (a b : Data R K T I H)

def event (rep : ℕ) (x : Types.VertexA rep) (y : Types.VertexB rep) (r : ActualPatternEvent.Match rep) : Prop :=
  OriginalPattern.Realized a.graph a.mark a.degree_two a.side a.side_edge a.paths a.nonempty
    a.root rep x y a.comparisons r

end

open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open GridAsymptotics GirthAsymptotics TypedGraphs
variable {R K T I H : ℕ} (a : Data R K T I H)

abbrev multiplicity := ChunkComparisons.multiplicity (color a.graph a.mark a.degree_two a.paths)
abbrev totalLength : ℝ := ∑ p, (((a.paths p).flatMap (word a.graph a.mark a.degree_two)).length:ℝ)

structure Good (B Q M J rep : ℕ) : Prop where
  multiplicity_le : ∀ c,a.multiplicity c≤M
  multiplicity_pos : ∀ c,1≤a.multiplicity c
  path_chain : ∀ p,List.IsChain (WeightedMoore.PortWalk.step
    (suppressed a.graph a.mark a.degree_two).origin (suppressed a.graph a.mark a.degree_two).reverse) (a.paths p)
  cyclic_chain : ∀ p,StageRoot.cyclic a.root p=true →
    ∀ᵉ (x∈(a.paths p).getLast?) (y∈(a.paths p).head?),
      WeightedMoore.PortWalk.step (suppressed a.graph a.mark a.degree_two).origin
        (suppressed a.graph a.mark a.degree_two).reverse x y
  reduced : ∀ x e,a.comparisons.side x=some e →
    originalDart a.graph a.mark a.degree_two a.paths x≠
      originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x) ∧
    originalDart a.graph a.mark a.degree_two a.paths x≠a.graph.reverse
      (originalDart a.graph a.mark a.degree_two a.paths (a.comparisons.pairing.partner x))
  chains_le : Fintype.card (Rep a.graph a.mark a.degree_two)≤Q
  cut_comparisons_le : Fintype.card a.E*(Fintype.card (RepeatedBlocks.Traversal a.multiplicity))^2≤J
  length_le : a.totalLength≤B*(L (size rep):ℝ)
  length_ge : (L (size rep):ℝ)≤a.totalLength
  unpaired_le : ((Finset.univ.filter (fun x => a.comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*a.totalLength

end TorsionFreeZeroDivisors.BoundedPattern.Data

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.ActualComplexity
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression
open ChainSuppression SuppressedMoore ChainPaths ChainIsomorphism ChainChunkTransport
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P] (Γ : PortGraph V D)

variable (paths : P → List D) (hp : ∀ p,paths p≠[])

end TorsionFreeZeroDivisors.ActualComplexity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RawDecomposition
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open GirthAsymptotics TypedGraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (raw : P → List D) (hp : ∀ p,raw p≠[])
    (hc : ∀ p,(raw p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))

def dart (x : Position (fun p => (raw p).length)) : D := (raw x.1).get ⟨x.2.val.toNat,by
  have hx := x.2.property
  have hz : 0≤x.2.val ∧ x.2.val<(raw x.1).length := by
    simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hx
  omega⟩

end TorsionFreeZeroDivisors.RawDecomposition

namespace TorsionFreeZeroDivisors.ComparisonGeometry

section
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}

variable [Fintype P]
end
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.RawSourcePattern

section
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open GirthAsymptotics TypedGraphs ActualPatternEvent

namespace Data
variable {B K I rep : ℕ}

end Data
end
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

end TorsionFreeZeroDivisors.RawSourcePattern
namespace TorsionFreeZeroDivisors.DiameterCounting
open scoped BigOperators Classical
open ConditionedMatchings
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V)

variable {label : D → T} {bar : T → T}

end TorsionFreeZeroDivisors.DiameterCounting

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ExpansionDiameter
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

end TorsionFreeZeroDivisors.ExpansionDiameter

namespace TorsionFreeZeroDivisors.DiameterProbability
open scoped BigOperators Topology Classical
open Filter

end TorsionFreeZeroDivisors.DiameterProbability

namespace TorsionFreeZeroDivisors.MatchingDiameter
open scoped Classical BigOperators
open ConditionedMatchings
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V) {label : D → T} {bar : T → T}

def simpleGraph (r : Matching label bar) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e : D, origin e=v ∧ origin (r e)=w
  symm := ⟨by
    rintro v w ⟨h,e,he,hef⟩
    exact ⟨h.symm,r e,hef,by rw [r.reverse_reverse,he]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end TorsionFreeZeroDivisors.MatchingDiameter

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

def p₀ : ℝ := 129/(4*16513)
def C₀ : ℝ := 9*(12*(132:ℝ)^2/p₀)^65
def ρ : ℝ := min (1/4) (min (p₀/65) (1/(2*C₀+2)))

abbrev ΩA (rep : ℕ) := Matching.conditioned
  (label:=TypedGraphs.label (@outgoingA rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingA rep)) (3*L (size rep)) ∅
abbrev ΩB (rep : ℕ) := Matching.conditioned
  (label:=TypedGraphs.label (@outgoingB rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingB rep)) (3*L (size rep)) ∅

def A₀ : ℕ := ⌈1/ρ⌉₊
def D₀ : ℕ := (A₀+1)*803

def diameterBadA (rep : ℕ) := (ΩA rep).filter fun r =>
  ∃ u v, (simpleGraph (TypedGraphs.origin (@outgoingA rep)) r).Reachable u v ∧
    D₀*L (size rep) < (simpleGraph (TypedGraphs.origin (@outgoingA rep)) r).dist u v
def diameterBadB (rep : ℕ) := (ΩB rep).filter fun r =>
  ∃ u v, (simpleGraph (TypedGraphs.origin (@outgoingB rep)) r).Reachable u v ∧
    D₀*L (size rep) < (simpleGraph (TypedGraphs.origin (@outgoingB rep)) r).dist u v

end TorsionFreeZeroDivisors.TypedDiameter
namespace TorsionFreeZeroDivisors.FiniteJointAvoidance
open scoped Classical
end TorsionFreeZeroDivisors.FiniteJointAvoidance

namespace TorsionFreeZeroDivisors.MatchingAlias
open scoped Classical
end TorsionFreeZeroDivisors.MatchingAlias

namespace TorsionFreeZeroDivisors.GraphSample
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

def Diameters (rep : ℕ) (r : Match rep) : Prop :=
  (∀ u v,(MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingA rep)) r.1).Reachable u v →
    (MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingA rep)) r.1).dist u v≤TypedDiameter.D₀*L (size rep)) ∧
  (∀ u v,(MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingB rep)) r.2).Reachable u v →
    (MatchingDiameter.simpleGraph (TypedGraphs.origin (@Types.outgoingB rep)) r.2).dist u v≤TypedDiameter.D₀*L (size rep))

end TorsionFreeZeroDivisors.GraphSample

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedGirth
open scoped Classical BigOperators
open PortSubdivision
variable {V D : Type} (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.WeightedGirth
namespace TorsionFreeZeroDivisors.SumGirth
open SimpleGraph
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
end TorsionFreeZeroDivisors.SumGirth
namespace TorsionFreeZeroDivisors.SumPort

section
open PortSubdivision SimpleGraph
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def graph : PortGraph (VA⊕VB) (DA⊕DB) where
  origin := Sum.map A.origin B.origin
  reverse := Sum.map A.reverse B.reverse
  reverse_reverse := by intro d; cases d <;> simp
  reverse_ne := by
    intro dart equality
    cases dart with
    | inl dart => exact A.reverse_ne dart (Sum.inl.inj equality)
    | inr dart => exact B.reverse_ne dart (Sum.inr.inj equality)
end
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph

section
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
abbrev VA := Types.VertexA rep
abbrev VB := Types.VertexB rep
abbrev DA := TypedGraphs.Dart (@Types.outgoingA rep)
abbrev DB := TypedGraphs.Dart (@Types.outgoingB rep)
def A : PortGraph (VA rep) (DA rep) := r.1.graph (TypedGraphs.origin (@Types.outgoingA rep))
def B : PortGraph (VB rep) (DB rep) := r.2.graph (TypedGraphs.origin (@Types.outgoingB rep))
def graph := SumPort.graph (A rep r) (B rep r)
def label : DA rep⊕DB rep → Types.Letter := Sum.elim (TypedGraphs.label _) (TypedGraphs.label _)
end
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks GirthAsymptotics TypedGraphs ActualPatternEvent
structure BoundedSystem (Bnd K I rep : ℕ) (r : Match rep) (x : VA rep) (y : VB rep) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List (DA rep⊕DB rep)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y
  length_le : (∑p,(paths p).length:ℕ)≤Bnd*L (size rep)
  length_ge : L (size rep)≤(∑p,(paths p).length:ℕ)
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠(graph rep r).reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*(∑p,(paths p).length:ℕ)
  rootA : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inl z) → z=x
  rootB : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inr z) → z=y
  compatible : ∀ p e,comparisons.side p=some e → label rep (RawDecomposition.dart paths p)=
    if comparisons.reverse e then Types.inverse (label rep (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label rep (RawDecomposition.dart paths (comparisons.pairing.partner p))
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ShortClosure
open scoped Classical
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

def simpleGraph : SimpleGraph V where
  Adj a b := a≠b ∧ ∃ d,Γ.origin d=a ∧ Γ.origin (Γ.reverse d)=b
  symm := ⟨by
    rintro a b ⟨hab,d,ha,hb⟩
    exact ⟨hab.symm,Γ.reverse d,hb,by simpa⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def edgeDart {a b : V} (h : (simpleGraph Γ).Adj a b) : D := h.2.choose
lemma edgeDart_start {a b : V} (h : (simpleGraph Γ).Adj a b) : Γ.origin (edgeDart Γ h)=a :=
  h.2.choose_spec.1
lemma edgeDart_end {a b : V} (h : (simpleGraph Γ).Adj a b) : Γ.origin (Γ.reverse (edgeDart Γ h))=b :=
  h.2.choose_spec.2

lemma dart_reachable (d : D) : (simpleGraph Γ).Reachable (Γ.origin d) (Γ.origin (Γ.reverse d)) := by
  by_cases h : Γ.origin d=Γ.origin (Γ.reverse d)
  · exact h ▸ SimpleGraph.Reachable.refl (G:=simpleGraph Γ) (Γ.origin d)
  · exact (show (simpleGraph Γ).Adj _ _ from ⟨h,d,rfl,rfl⟩).reachable

variable [Fintype V] [Fintype D]

end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SumPort
open PortSubdivision
open scoped Classical BigOperators
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
variable [Fintype DA] [Fintype DB]
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop)

variable [Fintype T]
end TorsionFreeZeroDivisors.RestrictComparisons

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.FiniteClusters
open scoped Classical BigOperators
variable {V : Type} [Fintype V] (G : SimpleGraph V)
local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

end TorsionFreeZeroDivisors.FiniteClusters

namespace TorsionFreeZeroDivisors.PairingClusters
open scoped Classical BigOperators
variable {O T : Type} [Fintype O] [Fintype T]
    (f : O → T) (α : O → O) (hα : Function.Involutive α) (keep : T → Prop)
def Rel (p q : T) : Prop := ∃ o,f o=p ∧ f (α o)=q
end TorsionFreeZeroDivisors.PairingClusters

namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.PlanarLocalization

namespace TorsionFreeZeroDivisors.ClusterLocalization
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)

end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ClusterLocalization

section
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
end

open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] [Fintype E] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
end TorsionFreeZeroDivisors.ClusterLocalization
namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical
variable {T : Type} (root : Option T) (keep : T → Prop)
end TorsionFreeZeroDivisors.RestrictComparisons

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks GirthAsymptotics TypedGraphs ActualPatternEvent

structure PathSystem (rep : ℕ) (r : Match rep) (x : VA rep) (y : VB rep) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List (DA rep⊕DB rep)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠(graph rep r).reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  rootA : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inl z) → z=x
  rootB : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inr z) → z=y
  compatible : ∀ p e,comparisons.side p=some e → label rep (RawDecomposition.dart paths p)=
    if comparisons.reverse e then Types.inverse (label rep (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label rep (RawDecomposition.dart paths (comparisons.pairing.partner p))
attribute [instance] PathSystem.fP PathSystem.fE
namespace PathSystem
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
end PathSystem
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open ComparedBlocks GirthAsymptotics TypedGraphs ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BalancedPieces
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.BalancedPieces
namespace TorsionFreeZeroDivisors.ConsecutivePieces
open scoped Classical BigOperators
variable {A : Type*} {m : ℕ} (l : List A) (n : Fin m → ℕ) (hs : (∑ i,n i)=l.length)

end TorsionFreeZeroDivisors.ConsecutivePieces
namespace TorsionFreeZeroDivisors.BalancedWords
open scoped Classical BigOperators
variable {T A : Type} (w : T → List A) (cap : ℕ) (hc : 0<cap)

variable [Fintype T]
end TorsionFreeZeroDivisors.BalancedWords
namespace TorsionFreeZeroDivisors.ShortClosure
open PortSubdivision WeightedMoore.PortWalk
variable {V D : Type} (Γ : PortGraph V D)
end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)

abbrev D : ℕ := TypedDiameter.D₀+1608

end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
abbrev Cycle := Quotient (Equiv.Perm.SameCycle.setoid f)
instance : Fintype (Cycle f) := Fintype.ofFinite _

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
def opposite : Equiv.Perm O := α*σ

def Good (x : O) : Prop :=
  opposite σ α (opposite σ α x)=x ∧ opposite σ α x≠x ∧ σ x≠x
end TorsionFreeZeroDivisors.PlanarRotation
namespace TorsionFreeZeroDivisors.PlanarRuns
open scoped Classical BigOperators
open PlanarRotation
variable {O : Type}

structure CutSystem (σ : Equiv.Perm O) where
  cut : Finset O
  hits : ∀ x, ∃ n : ℕ, (σ^n) x∈cut

namespace CutSystem
variable {σ : Equiv.Perm O} (S : CutSystem σ)

structure Paired (α : Equiv.Perm O) : Prop where
  involutive : Function.Involutive α
  fixed_free : ∀ x, α x≠x
  good : ∀ x, x∉S.cut → Good σ α x
  stable : ∀ x, Good σ α x → (x∈S.cut ↔ opposite σ α x∈S.cut)

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
variable [Fintype A]
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
end Paired

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

lemma position_ext {x y : Position len} (hs : x.1=y.1) (hc : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,q⟩; rcases y with ⟨y,r⟩
  dsimp at hs hc
  subst y
  congr 1
  exact Subtype.ext hc

include hstep
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

variable (hupper : ∀ e,C.hi e≤len (C.source e))

variable [Fintype T]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
lemma bounds {n : ℕ} (q : {z // z∈positions 0 (n:ℝ)}) : 0≤q.val ∧ q.val<(n:ℤ) := by
  simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using q.property
variable {T : Type} (len : T → ℕ)
def fin : Position len ≃ ((t : T) × Fin (len t)) where
  toFun x := ⟨x.1,⟨x.2.val.toNat,by
    have hx := bounds x.2
    omega⟩⟩
  invFun x := ⟨x.1,⟨x.2.val,by
    simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using
      (show (0:ℤ)≤x.2.val ∧ (x.2.val:ℤ)<len x.1 from ⟨by omega,by exact_mod_cast x.2.isLt⟩)⟩⟩
  left_inv x := by
    apply PlanarIntervals.position_ext
    · rfl
    · have hx := bounds x.2
      dsimp only
      omega
  right_inv x := by
    rcases x with ⟨t,i⟩
    simp only [Int.toNat_natCast]
variable {A : Type} (w : T → List A)

variable (cap : ℕ) (hc : 0<cap)
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
variable {A : Type} (w v : T → List A)
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r) {E : Type} [Fintype E] (lo hi : E → ℕ) (hle : ∀ e,lo e≤hi e)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.BoundaryRotation

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T : Type} (len : T → ℕ)
def perm : Equiv.Perm (Position len) :=
  (fin len).symm.permCongr (Equiv.sigmaCongrRight fun t=>finRotate (len t))
variable [Fintype T]
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T) (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len)) (hr : Function.Involutive α) (hcomp : ∀ x,label (α x)=bar (label x))
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A) (R : A → A → Prop)
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.BalancedRotation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (w : T → List A) (cap : ℕ) (hc : 0<cap)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
namespace FullPairing
variable {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end FullPairing
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent PermutationCycles PlanarRotation
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

structure Split (S : Finset V) where
  remove : Finset V
  parts : Finset (Finset V)
  remove_subset : remove⊆S
  cover : parts.biUnion id=S\remove
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  closed : ∀ b∈parts,∀ x∈b,∀ y∈S\remove,R x y → y∈b
  size : ∀ b∈parts,3*b.card≤2*S.card
  cost : (remove.card : ℝ)≤2*Real.sqrt 2*Real.sqrt S.card

namespace Split
variable {R} {S : Finset V} (P : Split R S)
end Split

def q : ℝ := Real.sqrt (2/3)
def a : ℝ := 2*Real.sqrt 2
def Csep : ℝ := a/(1-q)

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
end Split

end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
def U : ℕ := max 3 ⌈96*(D:ℝ)/ε⌉₊
def η : ℝ := min (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
def K : ℕ := max 1 ⌈(Csep/η ε D)^2⌉₊
def C : ℕ := K ε D*(U ε D+D)
def C₂ : ℕ := 32*6

def sides : ℕ := 2*C₂*C ε D
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)

end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks
abbrev ε : ℝ := StageFusion.epsilon (1/600) 256
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (hL : 2≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

variable [Fintype O]

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

def Edge (σ α : Equiv.Perm O) (x y : O) : Prop := σ x=y ∨ α x=y
abbrev Component (σ α : Equiv.Perm O) := Quotient (Relation.EqvGen.setoid (Edge σ α))
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)

def GenusZero : Prop :=
  2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))=α.support.card+4*Nat.card (Component σ α)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
end
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)

variable (hs : σ p≠p)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler

namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

namespace Ear
variable (k : ℕ)

variable {inv : A → A} {label : Fin n → A}
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

def inverseLetter (p : A × Bool) : A × Bool := (p.1,!p.2)

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
variable (k : ℕ) (hk : k≤n) (hn : 0<n)

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Ear
variable (k : ℕ) (hk : k≤n)
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A} (k : ℕ) (hk : k≤n)
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
variable [Fintype O]
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
variable (p q : O) (hpq : p≠q)
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O) (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α) (he : ∀e∈l,α e.1=e.2)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
variable [Fintype A] [Fintype B]
end TorsionFreeZeroDivisors.MapConjugation

namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)

variable (before after : O→V)
end TorsionFreeZeroDivisors.Tightening

namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
end TorsionFreeZeroDivisors.Tightening
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V) [Fintype O]
namespace Data
variable {Γ label inv x y}

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.FinitePicture

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V}
variable (hxy : x≠y)
end TorsionFreeZeroDivisors.FinitePicture.Data

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {A : Type*}
open FreeGroup

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

inductive Path : V→V→Type
  | nil (v : V) : Path v v
  | cons (d : D) {b : V} (p : Path (Γ.origin (Γ.reverse d)) b) : Path (Γ.origin d) b
namespace Path
variable {Γ} {a b c : V}
def append : {a b c : V} → Path Γ a b→Path Γ b c→Path Γ a c
  | _,_,_,.nil _,q => q
  | _,_,_,.cons d p,q => .cons d (p.append q)
def single (d : D) : Path Γ (Γ.origin d) (Γ.origin (Γ.reverse d)) := .cons d (.nil _)
def cast {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) : Path Γ a' b' := by
  subst a'; subst b'; exact p

def eval {G : Type*} [_root_.Group G] (label : D→G) : {a b : V} → Path Γ a b→G
  | _,_,.nil _ => 1
  | _,_,.cons d p => label d*p.eval label

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
variable {A : Type*} (label : D→A×Bool)

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
variable [Fintype O]

end TorsionFreeZeroDivisors.MarkerInsertion
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V)
  (σ α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀i,α i≠i)
  (edge : O→D) (p : O)
  (hc : ∀i,label (edge (α i))=inv (label (edge i)))
  (hj : ∀i,σ i≠p → Γ.origin (Γ.reverse (edge i))=Γ.origin (edge (σ i)))
  (hp : Γ.origin (edge p)=x)
  (he : ∀i,σ i=p → Γ.origin (Γ.reverse (edge i))=y)
  (hz : MapEuler.GenusZero σ α)

end TorsionFreeZeroDivisors.FinitePicture

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
variable {x y : V} (p : Path Γ x y)

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

structure Routes where
  base : V→V
  same : ∀ d,base (Γ.origin d)=base (Γ.origin (Γ.reverse d))
  path : ∀ v,Path Γ (base v) v

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)
def word (v : V) : FreeGroup S := (R.path v).eval letters
def relator (d : D) : FreeGroup S :=
  word Γ letters R (Γ.origin d)*letters d*(word Γ letters R (Γ.origin (Γ.reverse d)))⁻¹
def relations : Set (FreeGroup S) := Set.range (relator Γ letters R)
abbrev Group := PresentedGroup (relations Γ letters R)
def value (v : V) : Group Γ letters R := PresentedGroup.mk _ (word Γ letters R v)

instance [Finite S] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (relator Γ letters R) |>.to_subtype
  infer_instance

end

open scoped Classical
open PortSubdivision
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d)) (R : Routes Γ)

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
variable {V D A B O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (f : A→B) (label' : D→B) (inv' : B→B) (hl : ∀d,label' d=f (label d)) (hf : ∀t,f (inv t)=inv' (f t))

end TorsionFreeZeroDivisors.FinitePicture.Data
namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ}
def ofWalk : {a b : V} → (ShortClosure.simpleGraph Γ).Walk a b→Path Γ a b
  | _,_,.nil => .nil _
  | _,_,.cons h p =>
    ((Path.single (Γ:=Γ) (ShortClosure.edgeDart Γ h)).cast
      (ShortClosure.edgeDart_start Γ h) (ShortClosure.edgeDart_end Γ h)).append (ofWalk p)
end Path
def routes : Routes Γ where
  base v := (ShortClosure.simpleGraph Γ).connectedComponentMk v |>.out
  same d := congrArg Quot.out (SimpleGraph.ConnectedComponent.sound (ShortClosure.dart_reachable Γ d))
  path v := Path.ofWalk (Classical.choice (SimpleGraph.ConnectedComponent.eq.mp
    ((ShortClosure.simpleGraph Γ).connectedComponentMk v).out_eq))

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.ConcreteGroup

section
open scoped Classical BigOperators
open PortSubdivision TypedGraphs ConditionedMatchings SampleGraph

def freeLetter (t : Types.Letter) : FreeGroup Types.Generator :=
  if (Types.signedLetter.symm t).2 then FreeGroup.of (Types.signedLetter.symm t).1
  else (FreeGroup.of (Types.signedLetter.symm t).1)⁻¹
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
abbrev Γ := SampleGraph.graph rep r
def labels : DA rep⊕DB rep → FreeGroup Types.Generator := freeLetter ∘ SampleGraph.label rep
def routes := GraphPresentation.routes (Γ rep r)
abbrev G := GraphPresentation.Group (Γ rep r) (labels rep) (routes rep r)
def value : VA rep⊕VB rep → G rep r := GraphPresentation.value (Γ rep r) (labels rep) (routes rep r)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
end

open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
open PortSubdivision PermutationCycles
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A)

structure Data where
  rotation : Equiv.Perm O
  partner : Equiv.Perm O
  involutive : Function.Involutive partner
  fixed_free : ∀ i,partner i≠i
  dart : O→D
  consistent : ∀ i,Γ.origin (Γ.reverse (dart i))=Γ.origin (dart (rotation i))
  compatible : ∀ i,label (dart (partner i))=inv (label (dart i))
  genusZero : MapEuler.GenusZero rotation partner
namespace Data
variable {Γ label inv} (a : Data (O:=O) Γ label inv)

def Reduced : Prop := (∀i,a.dart (a.partner i)≠Γ.reverse (a.dart i)) ∧
  ∀i,a.dart (a.rotation i)≠Γ.reverse (a.dart i)

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)

variable (hr : a.Reduced)
end Data
end TorsionFreeZeroDivisors.SphericalPicture

namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
  {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)

end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortSubdivision.PortGraph V D) (label : D→A) (inv : A→A)
variable {Γ label inv}
namespace Data
variable {O : Type} [Fintype O] (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.SphericalPicture
namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortGraph V D) (R : Routes Γ)
variable (label : D→A) (inv : A→A)
variable {Γ R label inv} {O : Type} [Fintype O]
variable (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
end TorsionFreeZeroDivisors.ConePicture

end

end OAI
end

section
namespace OAI

section
namespace TorsionFreeZeroDivisors.ConeSigned
open scoped Classical
open PortSubdivision GraphPresentation
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
def freeLetter {A : Type} (a : A×Bool) : FreeGroup A := FreeGroup.mk [a]
local notation "letters" => freeLetter ∘ label

end
end TorsionFreeZeroDivisors.ConeSigned

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedComponent
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings TypedGraphs
variable {V : Type} (outgoing : V→Finset Types.Letter)
    (r : Matching (label outgoing) Types.inverse) (root : V)
abbrev graph := r.graph (origin outgoing)
abbrev Vertex := {v : V // (ShortClosure.simpleGraph (graph outgoing r)).Reachable root v}
end TorsionFreeZeroDivisors.TypedComponent

namespace TorsionFreeZeroDivisors.ComponentFactors
open scoped Classical BigOperators
open ConditionedMatchings TypedGraphs TypedComponent SampleGraph
variable {G : Type} [_root_.Group G] (rep : ℕ) (r : ActualPatternEvent.Match rep)
  (x : SampleGraph.VA rep) (y : SampleGraph.VB rep)
abbrev CA := TypedComponent.Vertex (@Types.outgoingA rep) r.1 x
abbrev CB := TypedComponent.Vertex (@Types.outgoingB rep) r.2 y
end TorsionFreeZeroDivisors.ComponentFactors

namespace TorsionFreeZeroDivisors.ConcreteFactors
open scoped Classical BigOperators
open TypedGraphs ConditionedMatchings SampleGraph ConcreteGroup TypedComponent
variable (rep : ℕ) (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
def leftValue (a : ComponentFactors.CA rep r x) : G rep r :=
  (value rep r (Sum.inl x))⁻¹*value rep r (Sum.inl a.val)
def rightValue (b : ComponentFactors.CB rep r y) : G rep r :=
  (value rep r (Sum.inr y))⁻¹*value rep r (Sum.inr b.val)
def alpha : MonoidAlgebra (ZMod 2) (G rep r) :=
  ∑ a,MonoidAlgebra.single (leftValue rep r x a) 1
def beta : MonoidAlgebra (ZMod 2) (G rep r) :=
  ∑ b,MonoidAlgebra.single ((rightValue rep r y b)⁻¹) 1
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SumPort
open scoped Classical
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.ConcreteFactors

section
open scoped Classical
open SampleGraph ConcreteGroup
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep) (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep) (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hsample havoid

end
open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical
open Filter GirthAsymptotics TypedGraphs
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors
end TorsionFreeZeroDivisors

end

end OAI
end


