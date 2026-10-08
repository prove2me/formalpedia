-- Prove2me | Definitions.Def_CantorSystems
-- name    : CantorSystems
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T14:43:59.425747+00:00
-- url     : https://prove2.me/theorems/fea7f322-a499-4cb3-b654-f75857b5997e
-- title:
--   Topological full groups, Cantor spaces and subshifts
-- statement:
--   The definitions behind Matte Bon's theorem on random walks on topological full groups of subshifts (N. Matte Bon, arXiv:1402.2234v2, cited MB) and its use by Juschenko, Matte Bon, Monod and de la Salle (JMMS, arXiv:1503.04977v1, §5.3), written for any group acting so that a later mission on topological full groups can reuse them. Groups act additively, so that $\mathbf Z$ and subgroups $\Lambda$ of $\mathbf R/\mathbf Z$ act by $+_v$.
--
--   **Topological full group.** JMMS, p. 20: “Let $\Gamma$ be a group acting by homeomorphisms on a topological space $X$. The topological full group of the action, $[[\Gamma]]$, is the group of all homeomorphisms $h$ of $X$ such that every point of $X$ admits a neighborhood where $h$ agrees with an element of $\Gamma$.” This is `topologicalFullGroup Γ X`, a subgroup of the homeomorphism group of $X$; for $\Gamma = \mathbf Z$ acting by the powers of $\tau$ it is MB's $[[\tau]]$ (MB, p. 2).
--
--   **Cantor spaces.** MB (p. 2) and JMMS (p. 20) speak of “the Cantor set”. `IsCantorSpace X` says $X$ is nonempty, compact, metrizable, totally disconnected and has no isolated points.
--
--   **Subshifts.** MB, p. 2: “A subshift is a Cantor system $(\Sigma, \tau)$ where $\Sigma \subset A^{\mathbb Z}$ is a closed subset which is invariant under the shift.” JMMS, p. 20: “A $\Gamma$-subshift is a Cantor $\Gamma$-system $(\Gamma, X)$ where $X \subset A^\Gamma$ is a closed $\Gamma$-invariant subset.” Here $\Gamma$ acts on $A^\Gamma$ by $(\gamma \cdot x)(\delta) = x(\delta + \gamma)$ (`shift`), so that for $\Gamma = \mathbf Z$ the generator acts as MB's $\tau : (x_i) \mapsto (x_{i+1})$; $A^\Gamma$ carries the product of the discrete topologies. A `Subshift Γ A` is a closed shift-invariant subset, with the shift action on its points. Being a Cantor space is not part of the definition; statements that need it say so. Mathlib's `SymbolicDynamics.Subshift` is the same notion for commutative $\Gamma$; it shifts by $x \mapsto x(\gamma + \cdot)$, which is an action only when $\Gamma$ is commutative, so the bundle keeps its own shift, an action for every group, as JMMS's Lemma 5.10 is stated for any $\Gamma$.
--
--   **Complexity.** MB, p. 2: “The complexity of a subshift $(\Sigma, \tau)$ is the function $\rho : \mathbb N \to \mathbb N$ that counts the number of words of length $n$ in the alphabet $A$ that appear as sub-words of sequences in $\Sigma$.” This is `wordComplexity`, counting words $w$ of length $n$ with $x_{i+j} = w_j$ ($0 \le j < n$) for some $x \in \Sigma$ and some position $i \in \mathbf Z$. JMMS, p. 21: “The one-dimensional complexity of the subshift $(\Gamma, X)$ with respect to $S$ and $P$ is the function $\rho_{S,P} : \mathbb N \to \mathbb N$ that counts the number of elements of the partition $\bigvee_{|\gamma|_S \le n} \gamma P$, where $|\cdot|_S$ is the word metric associated to $S$.” This is `complexity T p n`, with the finite partition $P$ given as a map $p : X \to \iota$ ($\iota$ finite, pieces the fibres) and the generating set written $T$; `IsClopenPartition p` says the pieces are clopen and `IsSeparatingPartition Γ p` says that, as in JMMS Lemma 5.10, “for any $x \ne y \in X$ there exists $\gamma \in \Gamma$ so that the partition $\gamma P$ separates $x$ and $y$”.
--
--   **The groups $\mathrm{IET}(\Lambda; \Sigma)$.** JMMS, p. 21: “We denote $\mathrm{IET}(\Lambda; \Sigma)$ the subgroup of $\mathrm{IET}(\Lambda)$ consisting of interval exchange transformations so that all extrema of the defining intervals lie in cosets $x_i + \Lambda$ of points in $\Sigma$.” This is `IETOn Λ σ` (the finite set $\Sigma$ is written $\sigma$), with `cosetsOf Λ σ` $= \Sigma + \Lambda$.
--
--   *Formalization note.* “All extrema of the defining intervals lie in $\Sigma + \Lambda$” is encoded as: $g$ and $g^{-1}$ are continuous at every point outside $\Sigma + \Lambda$. For an interval exchange the discontinuities are the extrema of its coarsest defining intervals, and when $\Sigma$ is nonempty a continuous one (a rotation) can be cut at a point of $\Sigma$, so the two readings agree; the clause on $g^{-1}$ is automatic and makes the subgroup laws immediate.
-- source:
--   Matte Bon, N., Subshifts with slow complexity and simple groups with the Liouville property, Geom. Funct. Anal. 24 (2014) 1637–1659, https://doi.org/10.1007/s00039-014-0293-4 (arXiv:1402.2234v2, whose page numbers are used), p. 2, topological full groups, subshifts and complexity, and Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), pp. 20–21 (Cantor Γ-systems, Γ-subshifts, complexity ρ_{S,P}, IET(Λ; Σ))

import Mathlib
import Definitions.Def_IntervalExchange

/-!
# Topological full groups, Cantor systems and subshifts

N. Matte Bon, *Subshifts with slow complexity and simple groups with the Liouville property*,
Geom. Funct. Anal. 24 (2014) 1637–1659, arXiv:1402.2234v2 (MB), p. 2; K. Juschenko, N. Matte
Bon, N. Monod and M. de la Salle, *Extensive amenability and an application to interval
exchanges*, Ergodic Theory Dynam. Systems 38 (2018) 195–219, arXiv:1503.04977v1 (JMMS),
§5.3, pp. 20–21. Page numbers are those of the arXiv versions.

Conventions:
- Groups acting here are additive (`AddGroup Γ`, `AddAction Γ X`), so that `ℤ` and the subgroups
  `Λ` of `ℝ/ℤ` act by `+ᵥ`.
- The shift of `Γ` on `A^Γ = Γ → A` is `(γ +ᵥ x) δ = x (δ + γ)`. For `Γ = ℤ`, `1 +ᵥ x` is Matte
  Bon's shift `τ`, `(τ x)_i = x_{i+1}`. The topology on `Γ → A` is the product topology; every
  statement using it assumes `[DiscreteTopology A]`, so it is the product of the discrete
  topology on `A`.
- A finite partition of `X` is a map `p : X → ι` with `ι` finite: its pieces are the nonempty
  fibres `p ⁻¹' {i}`. A clopen partition has clopen fibres.
- Word balls of an additive group are sums of at most `n` elements of `T ∪ -T`.
- JMMS's finite set `Σ ⊂ ℝ/ℤ` is written `σ`, since `Σ` is reserved syntax in Lean.
-/

namespace CantorSystems

open Topology

/-! ## Topological full groups (MB p. 2, JMMS p. 20) -/

section FullGroup

variable (Γ X : Type*) [AddGroup Γ] [AddAction Γ X] [TopologicalSpace X]

/-- JMMS p. 20: "Let Γ be a group acting by homeomorphisms on a topological space X. The
topological full group of the action, [[Γ]], is the group of all homeomorphisms h of X such that
every point of X admits a neighborhood where h agrees with an element of Γ." For `Γ = ℤ` acting by
the iterates of `τ`, this is MB p. 2: "the group of homeomorphisms g ∈ Homeo(Σ) such that for every
x ∈ Σ there exists an open neighborhood U of x and an integer k ∈ Z for which g|U = τ^k|U".

The group laws hold for any action (continuous or not), since the members are homeomorphisms. -/
def topologicalFullGroup : Subgroup (X ≃ₜ X) where
  carrier := {h | ∀ x : X, ∃ U ∈ 𝓝 x, ∃ γ : Γ, ∀ y ∈ U, h y = γ +ᵥ y}
  one_mem' x := ⟨Set.univ, Filter.univ_mem, 0, fun y _ => by simp⟩
  mul_mem' {f g} hf hg x := by
    obtain ⟨U, hU, γ, hγ⟩ := hg x
    obtain ⟨V, hV, δ, hδ⟩ := hf (g x)
    refine ⟨U ∩ g ⁻¹' V, Filter.inter_mem hU (g.continuous.continuousAt.preimage_mem_nhds hV),
      δ + γ, fun y hy => ?_⟩
    rw [Homeomorph.mul_apply, hδ _ hy.2, hγ _ hy.1, add_vadd]
  inv_mem' {h} hh x := by
    obtain ⟨U, hU, γ, hγ⟩ := hh (h.symm x)
    refine ⟨h '' U, ?_, -γ, ?_⟩
    · have := h.isOpenMap.image_mem_nhds hU
      simpa using this
    · rintro _ ⟨u, hu, rfl⟩
      rw [Homeomorph.inv_apply, Homeomorph.symm_apply_apply, hγ u hu, neg_vadd_vadd]

end FullGroup

/-! ## Cantor spaces (MB p. 2, JMMS p. 20) -/

/-- MB p. 2 and JMMS p. 20 speak of "the Cantor set". Here `X` is a Cantor space when it is
nonempty, compact, metrizable, totally disconnected and has no isolated points; by Brouwer's
theorem these are exactly the spaces homeomorphic to the Cantor set. -/
def IsCantorSpace (X : Type*) [TopologicalSpace X] : Prop :=
  Nonempty X ∧ CompactSpace X ∧ TopologicalSpace.MetrizableSpace X ∧
    TotallyDisconnectedSpace X ∧ ∀ x : X, ¬ IsOpen ({x} : Set X)

/-! ## Subshifts (MB p. 2, JMMS p. 20) -/

section Subshift

variable {Γ A : Type*} [AddGroup Γ]

/-- MB p. 2, JMMS p. 20: the shift of `Γ` on `A^Γ`, by translations:
`(shift γ x) δ = x (δ + γ)`. For `Γ = ℤ`, `shift 1` is MB's
"τ : · · · x₋₂ x₋₁ .x₀ x₁ x₂ · · · ↦ · · · x₋₁ x₀ .x₁ x₂ x₃ · · ·". -/
def shift (γ : Γ) (x : Γ → A) : Γ → A := fun δ => x (δ + γ)

@[simp] lemma shift_apply (γ : Γ) (x : Γ → A) (δ : Γ) : shift γ x δ = x (δ + γ) := rfl

lemma shift_zero (x : Γ → A) : shift (0 : Γ) x = x := by
  funext δ; simp

lemma shift_add (γ γ' : Γ) (x : Γ → A) : shift (γ + γ') x = shift γ (shift γ' x) := by
  funext δ; simp [add_assoc]

variable [TopologicalSpace A]

/-- MB p. 2: "A subshift is a Cantor system (Σ, τ) where Σ ⊂ A^Z is a closed subset which is
invariant under the shift"; JMMS p. 20: "A Γ-subshift is a Cantor Γ-system (Γ, X) where
X ⊂ A^Γ is a closed Γ-invariant subset." Here: `S` is closed and shift-invariant. Being a Cantor
space is not part of this predicate; statements that need it assume `IsCantorSpace` separately. -/
def IsSubshift (S : Set (Γ → A)) : Prop :=
  IsClosed S ∧ ∀ γ : Γ, ∀ x ∈ S, shift γ x ∈ S

variable (Γ A) in
/-- A subshift of `A^Γ`, bundled, so that `↥S` carries the shift action. -/
structure Subshift where
  /-- The underlying closed shift-invariant set. -/
  carrier : Set (Γ → A)
  isSubshift : IsSubshift carrier

namespace Subshift

instance : SetLike (Subshift Γ A) (Γ → A) where
  coe := carrier
  coe_injective S T h := by cases S; cases T; congr

/-- The shift action of `Γ` on the points of a subshift. -/
instance (S : Subshift Γ A) : AddAction Γ S where
  vadd γ x := ⟨shift γ x, S.isSubshift.2 γ x x.2⟩
  zero_vadd x := Subtype.ext (shift_zero x.1)
  add_vadd γ γ' x := Subtype.ext (shift_add γ γ' x.1)

lemma coe_vadd (S : Subshift Γ A) (γ : Γ) (x : S) : ((γ +ᵥ x : S) : Γ → A) = shift γ x := rfl

end Subshift

end Subshift

/-! ## Complexity (MB p. 2, JMMS p. 21) -/

/-- MB p. 2: "The complexity of a subshift (Σ, τ) is the function ρ : N → N that counts the
number of words of length n in the alphabet A that appear as sub-words of sequences in Σ."
Here a word of length `n` is `w : Fin n → A`, and it is a sub-word of `x` when
`x (i + j) = w j` for some `i : ℤ` and all `j < n` (sub-words at any position, not only at
position `0`). -/
noncomputable def wordComplexity {A : Type*} (S : Set (ℤ → A)) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → A | ∃ x ∈ S, ∃ i : ℤ, ∀ j : Fin n, x (i + j) = w j}

section Complexity

variable {Γ X ι : Type*} [AddGroup Γ]

/-- JMMS p. 21: the word-metric ball `{γ : |γ|_T ≤ n}`, the sums of at most `n` elements of
`T ∪ -T`. -/
def wordBall (T : Set Γ) (n : ℕ) : Set Γ :=
  {γ | ∃ l : List Γ, l.length ≤ n ∧ (∀ t ∈ l, t ∈ T ∨ -t ∈ T) ∧ l.sum = γ}

/-- JMMS p. 21: the finite partition `p` (pieces `p ⁻¹' {i}`) is a partition into clopen sets. -/
def IsClopenPartition [TopologicalSpace X] (p : X → ι) : Prop :=
  ∀ i : ι, IsClopen (p ⁻¹' {i})

variable (Γ) [AddAction Γ X]

/-- JMMS Lemma 5.10, p. 21: "the partition ∨_{γ∈Γ} γP is the point partition of X (i.e. for any
x ≠ y ∈ X there exists γ ∈ Γ so that the partition γP separates x and y)". The pieces of `γP`
are the sets `γ +ᵥ p ⁻¹' {i} = {x | p (-γ +ᵥ x) = i}`; as `γ` runs over `Γ` so does `-γ`, so
`x` and `y` are separated by some `γP` iff `p (γ +ᵥ x) ≠ p (γ +ᵥ y)` for some `γ`. -/
def IsSeparatingPartition (p : X → ι) : Prop :=
  ∀ x y : X, (∀ γ : Γ, p (γ +ᵥ x) = p (γ +ᵥ y)) → x = y

variable {Γ}

/-- JMMS p. 21: "The one-dimensional complexity of the subshift (Γ, X) with respect to S and P is
the function ρ_{S,P} : N → N that counts the number of elements of the partition ∨_{|γ|_S ≤ n} γP,
where | · |_S is the word metric associated to S." The pieces of `γP` are
`{x | p (-γ +ᵥ x) = i}`, so the pieces of the join are the nonempty fibres of
`x ↦ (γ ↦ p (-γ +ᵥ x))` on the ball; their number is the number of values of this map. (The
generating set is written `T` here, since `S` names subshifts.) -/
noncomputable def complexity (T : Set Γ) (p : X → ι) (n : ℕ) : ℕ :=
  Nat.card (Set.range fun x : X => fun γ : wordBall T n => p (-(γ : Γ) +ᵥ x))

end Complexity

/-! ## The groups `IET(Λ; Σ)` (JMMS p. 21) -/

section IETOn

open IntervalExchange

/-- JMMS p. 21: the set `Σ + Λ`, the union of the cosets `xᵢ + Λ` of the points `xᵢ ∈ Σ`. -/
def cosetsOf (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) : Set UnitAddCircle :=
  {x | ∃ s ∈ σ, x - s ∈ Λ}

lemma apply_mem_cosetsOf_iff {Λ : AddSubgroup UnitAddCircle} {σ : Finset UnitAddCircle}
    {g : Equiv.Perm UnitAddCircle} (hg : g ∈ anglesIn Λ) (x : UnitAddCircle) :
    g x ∈ cosetsOf Λ σ ↔ x ∈ cosetsOf Λ σ := by
  have hx : g x - x ∈ Λ := hg x
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    have := Λ.sub_mem h hx
    simpa using this
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    have := Λ.add_mem hx h
    simpa using this

/-- JMMS p. 21: "We denote IET(Λ; Σ) the subgroup of IET(Λ) consisting of interval exchange
transformations so that all extrema of the defining intervals lie in cosets xᵢ + Λ of points in
Σ."

Encoding: "all extrema of the defining intervals lie in Σ + Λ" is read as "`g` is continuous at
every point outside `Σ + Λ`". For an interval exchange `g` the points of discontinuity are exactly
the extrema of the coarsest choice of defining intervals, and when `Σ` is nonempty `g` admits
defining intervals with all extrema in `Σ + Λ` iff its discontinuities lie in `Σ + Λ` (a
continuous `g` is a rotation, defined on one interval cut at a point of `Σ`). The clause on
`g⁻¹` is automatic for interval exchanges (`g⁻¹` is continuous at `g x` iff `g` is continuous at
`x`); it is included so that the subgroup laws are elementary. -/
def IETOn (Λ : AddSubgroup UnitAddCircle) (σ : Finset UnitAddCircle) :
    Subgroup (Equiv.Perm UnitAddCircle) where
  carrier := {g | g ∈ IETOf Λ ∧ ∀ x ∉ cosetsOf Λ σ,
    ContinuousAt (g : UnitAddCircle → UnitAddCircle) x ∧
      ContinuousAt ((g⁻¹ : Equiv.Perm UnitAddCircle) : UnitAddCircle → UnitAddCircle) x}
  one_mem' := ⟨(IETOf Λ).one_mem, fun x _ => ⟨continuous_id.continuousAt,
    continuous_id.continuousAt⟩⟩
  mul_mem' {g h} hg hh := by
    refine ⟨(IETOf Λ).mul_mem hg.1 hh.1, fun x hx => ⟨?_, ?_⟩⟩
    · have hhx : h x ∉ cosetsOf Λ σ := by
        rwa [apply_mem_cosetsOf_iff (inf_le_right (a := IET) hh.1)]
      exact (hg.2 _ hhx).1.comp (hh.2 x hx).1
    · have hgx : g⁻¹ x ∉ cosetsOf Λ σ := by
        rwa [apply_mem_cosetsOf_iff ((anglesIn Λ).inv_mem (inf_le_right (a := IET) hg.1))]
      rw [mul_inv_rev]
      exact (hh.2 _ hgx).2.comp (hg.2 x hx).2
  inv_mem' {g} hg := by
    refine ⟨(IETOf Λ).inv_mem hg.1, fun x hx => ⟨(hg.2 x hx).2, ?_⟩⟩
    rw [inv_inv]
    exact (hg.2 x hx).1

end IETOn

end CantorSystems


