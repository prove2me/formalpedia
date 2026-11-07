-- Prove2me | Definitions.Def_LipStableCA_Alloc
-- name    : LipStableCA_Alloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:37.043278+00:00
-- url     : https://prove2.me/theorems/e1eb6d7f-7022-4aa7-a4cb-7115fe5f76a3
-- title:
--   The auction model: valuation profiles, allocations, incidence distance, optimal welfare
-- statement:
--   Items $M=[m]$ are allocated to bidders $N=[n]$. A valuation $v_i:2^M\to\mathbb R_{\ge0}$ is normalized, $v_i(\emptyset)=0$, and monotone, $v_i(B)\le v_i(C)$ for $B\subseteq C$; $\mathcal V$ is the class of these valuations and a profile is a tuple $v\in\mathcal V^n$. An allocation is a tuple $T=(T_1,\dots,T_n)$ of pairwise disjoint bundles, where items may be left unallocated; $\mathcal A$ is the finite set of allocations. The incidence matrix is $X(T)_{ij}=\mathbf 1\{j\in T_i\}$ and the distance of two allocations is $\|X(S)-X(T)\|_1=\sum_{i,j}|X(S)_{ij}-X(T)_{ij}|$. The optimal welfare is $\mathrm{OPT}(v)=\max_{T\in\mathcal A}\sum_iv_i(T_i)$.
--
--   The module also fixes the tie-breaking used by Mechanisms 1 and 2: the first maximizer in a given linear order.
--
--   **Formalization Note.** A profile is a raw array of real functions, and validity is the separate predicate `IsProfile`, so rules are total functions. The conditions come from the published `ComplementFreeCA.CFRounding` definitions (normalized, monotone, allocation, welfare), which add nothing to the paper's. The helper `toAlloc` reads a raw tuple of bundles as an allocation, with fallback to the empty allocation; Mechanisms 1 and 3 build pairwise disjoint tuples, so the fallback is never taken.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), §2, pp.6–7; Def. 2.5, p.8

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

open ComplementFreeCA.CFRounding

namespace LipStableCA

/-- A valuation profile, unbundled: `n` real functions on the bundles of `Fin m`. Afshinmehr,
Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256
c5e4c53f…), §2, p.6. **Formalization Note.** Validity is the separate predicate `IsProfile`, and every
quantifier over reports below is restricted by it, so rules are total functions on raw profiles. -/
abbrev Profile (n m : ℕ) := Fin n → Finset (Fin m) → ℝ

/-- The class `V` of §2, p.6: normalized and monotone. Non-negativity follows from the two. -/
def IsValuation {m : ℕ} (u : Finset (Fin m) → ℝ) : Prop :=
  IsNormalized u ∧ IsMonotone u

/-- Strict monotonicity, §2, p.6: `u B < u C` whenever `B ⊊ C`. -/
def IsStrictlyMonotone {m : ℕ} (u : Finset (Fin m) → ℝ) : Prop :=
  ∀ B C : Finset (Fin m), B ⊂ C → u B < u C

/-- A profile in `Vⁿ`, §2, p.6. -/
def IsProfile {n m : ℕ} (v : Profile n m) : Prop :=
  ∀ i, IsValuation (v i)

/-- The set `A` of allocations, §2, p.7: tuples of pairwise disjoint bundles; items may stay
unallocated. -/
def Alloc (n m : ℕ) : Type :=
  {T : Fin n → Finset (Fin m) // IsAllocation T}

noncomputable instance (n m : ℕ) : Fintype (Alloc n m) :=
  haveI : Finite (Alloc n m) := inferInstanceAs (Finite {T : Fin n → Finset (Fin m) // IsAllocation T})
  Fintype.ofFinite _

noncomputable instance (n m : ℕ) : DecidableEq (Alloc n m) := Classical.decEq _

/-- Allocations form a finite discrete space. -/
instance (n m : ℕ) : MeasurableSpace (Alloc n m) := ⊤

instance (n m : ℕ) : MeasurableSingletonClass (Alloc n m) := ⟨fun _ => trivial⟩

/-- The empty allocation `∅` of §2, p.7. -/
def Alloc.empty (n m : ℕ) : Alloc n m :=
  ⟨fun _ => ∅, fun _ _ _ => Finset.disjoint_empty_left _⟩

instance (n m : ℕ) : Nonempty (Alloc n m) := ⟨Alloc.empty n m⟩

open Classical in
/-- A raw tuple of bundles read as an allocation. **Formalization Note.** Mechanisms 1 and 3 use this
to avoid a disjointness proof inside their definitions; the tuples they build are pairwise disjoint,
so the fallback to the empty allocation is never taken. -/
noncomputable def toAlloc {n m : ℕ} (T : Fin n → Finset (Fin m)) : Alloc n m :=
  if h : IsAllocation T then ⟨T, h⟩ else Alloc.empty n m

/-- The incidence matrix `X(T)ᵢⱼ = 1{j ∈ Tᵢ}`, §2, p.7. -/
noncomputable def incidence {n m : ℕ} (T : Alloc n m) (i : Fin n) (j : Fin m) : ℝ :=
  if j ∈ T.1 i then 1 else 0

/-- The entrywise distance `‖X(S) − X(T)‖₁`, §2, p.8. -/
noncomputable def l1Dist {n m : ℕ} (S T : Alloc n m) : ℝ :=
  ∑ i, ∑ j, |incidence S i j - incidence T i j|

/-- The optimal welfare `OPT(v) = max_{T ∈ A} W_v(T)`, §2, p.7. -/
noncomputable def opt {n m : ℕ} (v : Profile n m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun T : Alloc n m => welfare v T.1)

open Classical in
/-- The first element in the order `ord` among the maximizers of `f` on the nonempty finite set `s`.
This is the tie-breaking rule "ties broken by the fixed order" of Mechanisms 1 and 2 (pp.10, 14).
**Formalization Note.** `ord` is an explicit parameter, so one order is shared by every report, which
Observation 4.7(3) relies on. -/
noncomputable def firstMaximizerOn {α : Type*} (ord : LinearOrder α) (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) : α :=
  @Finset.min' α ord (s.filter (fun a => ∀ b ∈ s, f b ≤ f a)) (by
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s f hs
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hmax⟩⟩)

end LipStableCA


