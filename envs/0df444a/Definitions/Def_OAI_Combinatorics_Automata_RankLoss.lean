-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_RankLoss
-- name    : OAI_Combinatorics_Automata_RankLoss
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:05:14.822984+00:00
-- url     : https://prove2.me/theorems/d5e235dc-0a9d-49fa-9dc8-6311c97e11ce
-- title:
--   The rank-loss function $2^{\lfloor (h-2)/31\rfloor}$ and the rank-loss property of relation quotients
-- statement:
--   Write $\mathcal B(H)$ for the monoid of binary relations on a set $H$, and $\mathcal P(A)$ for the monoid of diagrams on a finite set $A$: perfect matchings of $A\sqcup A$, multiplied by gluing. The rank of a diagram is its number of through-strands, that is, of left ports matched to right ports.
--
--   1. **Rank-loss function.** For $h\in\mathbb{N}$,
--   $$
--   \operatorname{rl}(h)=2^{\lfloor (h-2)/31\rfloor},
--   $$
--   with truncated subtraction, so $\operatorname{rl}(h)=1$ for $h\le 32$.
--   2. **Rank-loss property.** For $h\in\mathbb{N}$, $\mathrm{RL}(h)$ is the following statement. Let $H$ and $A$ be finite sets with $|H|=h$, and let $M$ be a finite monoid. Let $\rho:M\to\mathcal P(A)$ be an injective monoid homomorphism, and let $\phi:M\to\mathcal B(H)$ be a surjective monoid homomorphism with unit lifts (every unit of $\mathcal B(H)$ is the image of a unit of $M$). Then for every idempotent $a\in M$ and all $x\neq y$ in $H$ with $\phi(a)=\Delta_H\cup\{(x,y)\}$,
--   $$
--   \operatorname{rl}(h)\ \le\ |A|-\operatorname{rank}\rho(a).
--   $$
--   3. **Deleted and retained points of a rectangle frame.** Take a rectangle frame in $H$: injective maps $\lambda:I\to H$ and $\mu:J\to H$ with disjoint images and a hub $h_0$ outside both, where $I$ and $J$ are finite. For $i\in I$ and $j\in J$ the deleted set is
--   $$
--   \mathrm{Del}(i,j)=\lambda(I\setminus\{i\})\ \cup\ \mu(J\setminus\{j\})\ \cup\ \{h_0\},
--   $$
--   and the retained set is $H\setminus\mathrm{Del}(i,j)$. A frame point $\lambda(k)$ is retained iff $k=i$, and $\mu(k)$ is retained iff $k=j$.
--   4. **Trivial corner.** The corner of a monoid at its identity is isomorphic to the monoid itself.
--
--   $\mathrm{RL}(h)$ is the central algebraic estimate behind the lower bound. It says that in a faithful diagram representation of a finite monoid that maps onto the relation monoid on $h$ points (with unit lifts), every idempotent lift of a one-edge relation has rank defect at least $\operatorname{rl}(h)$. Later results prove $\mathrm{RL}(h)$ for all $h$, by induction through corners at retained sets of rectangle frames. They deduce that $|A|\ge\operatorname{rl}(|H|)$ whenever $|H|\ge2$ and a finite monoid embeds into $\mathcal P(A)$ and maps onto $\mathcal B(H)$. This is then applied with $|A|=4(s+\delta)^2$ ports, $\delta\in\{1,2\}$, to bound the number of states $s$ of a two-way deterministic automaton for one-way liveness.
--
--   **Formalization Note** The definitions are `rankLoss`, `RankLossAt`, `RectangleFrame.deleted` (a `Finset`), `RectangleFrame.retained` and `Corner.oneEquiv`, with the simp lemmas `left_mem_retained` and `right_mem_retained`. In `RankLossAt` the types $H$, $A$ and $M$ range over `Type`. The subtraction on the right is natural-number subtraction; it never truncates, because rank is at most $|A|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/RankLoss.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/RankLoss.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations

namespace OAI

namespace OneWayLiveness

def rankLoss (h : ℕ) : ℕ := 2 ^ ((h - 2) / 31)

/-- A simultaneous rank-loss bound for relation quotients with unit lifts. -/
def RankLossAt (h : ℕ) : Prop :=
  ∀ (H A M : Type) [Fintype H] [Fintype A] [Monoid M] [Finite M],
    Fintype.card H = h →
    ∀ (ρ : M →* Pairing (A ⊕ A)), Function.Injective ρ →
    ∀ (φ : M →* BRel H), Function.Surjective φ → HasUnitLifts φ →
    ∀ (a : M), a * a = a → ∀ (x y : H), x ≠ y → φ a = BRel.addEdge x y →
      rankLoss h ≤ Fintype.card A - Pairing.rank (ρ a)

namespace RectangleFrame
open scoped Classical
variable {H I J : Type} [Fintype I] [Fintype J]
    (F : RectangleFrame H I J)

noncomputable def deleted (i : I) (j : J) : Finset H :=
  ((Finset.univ.erase i).image F.left ∪ (Finset.univ.erase j).image F.right) ∪ {F.hub}

def retained (i : I) (j : J) : Set H := {x | x ∉ F.deleted i j}

@[simp] lemma left_mem_retained (i k : I) (j : J) :
    F.left k ∈ F.retained i j ↔ k = i := by
  simp only [retained, Set.mem_ofPred_eq, deleted, Finset.mem_union, Finset.mem_image,
    Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hk
    exact h (Or.inl (Or.inl ⟨k, hk, rfl⟩))
  · rintro rfl ((⟨a, ha, he⟩ | ⟨b, _, he⟩) | he)
    · exact ha (F.left_injective he)
    · exact F.disjoint k b he.symm
    · exact F.left_ne_hub k he

@[simp] lemma right_mem_retained (i : I) (j k : J) :
    F.right k ∈ F.retained i j ↔ k = j := by
  simp only [retained, Set.mem_ofPred_eq, deleted, Finset.mem_union, Finset.mem_image,
    Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hk
    exact h (Or.inl (Or.inr ⟨k, hk, rfl⟩))
  · rintro rfl ((⟨a, _, he⟩ | ⟨b, hb, he⟩) | he)
    · exact F.disjoint a k he
    · exact hb (F.right_injective he)
    · exact F.right_ne_hub k he

end RectangleFrame

open scoped Classical

namespace Corner
variable {M : Type*} [Monoid M]
def oneEquiv : Corner (1 : M) (one_mul 1) ≃* M where
  toFun := Corner.val
  invFun x := ⟨x, one_mul x, mul_one x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
end Corner

end OneWayLiveness

end OAI


